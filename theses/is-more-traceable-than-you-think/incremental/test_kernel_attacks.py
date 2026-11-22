"""Actual-kernel rejection controls, sharing only a checked fixed bootstrap."""
import copy
import hashlib
import json
import os
from pathlib import Path
import shutil
import tempfile
import unittest

from .engine import canonical
from .lean import KernelError, KernelSession
from .pipeline import Program, make_engine


def rehash_compiler_suffix(snapshot):
    prefix = snapshot["prefix"]
    for row in snapshot["rows"]:
        descriptor = {"stage": "compile", "payload": row["operation"],
                      "deps": row["links"], "scope": row["scope"]}
        prefix = hashlib.sha256(canonical({
            "previous": prefix, "task": row["task"],
            "descriptor": descriptor, "value": row["artifact"],
        })).hexdigest()
    snapshot["tail"] = prefix


def rehash_execution_suffix(snapshot):
    prefix = snapshot["execution_prefix"]
    for row in snapshot["execution_rows"]:
        prefix = hashlib.sha256(canonical({
            "previous": prefix, "task": row["task"],
            "descriptor": row["descriptor"], "value": row["value"],
        })).hexdigest()
    snapshot["execution_tail"] = prefix


class KernelAttacks(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.lean = shutil.which(os.environ.get("LEAN", "lean"))
        if cls.lean is None:
            raise RuntimeError("Lean is required for the kernel attack suite; set LEAN")
        cls.bootstrap_temporary = tempfile.TemporaryDirectory()
        cls.addClassCleanup(cls.bootstrap_temporary.cleanup)
        cls.bootstrap = Path(cls.bootstrap_temporary.name) / "bootstrap"
        session = KernelSession(cls.bootstrap, lean=cls.lean)
        if session.count != 0 or session.execution_count != 0:
            raise AssertionError("bootstrap must contain only fixed checked modules")

    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.directory = self.root / "kernel"
        shutil.copytree(self.bootstrap, self.directory)
        self.session = KernelSession(self.directory, lean=self.lean)
        self.engine = make_engine(self.root / "history.jsonl")
        self.addCleanup(lambda: self.engine.close() if not self.engine._stream.closed else None)
        self.program = Program(self.engine, {
            "x": {"op": "input", "value": 2},
            "three": {"op": "const", "value": 3},
            "out": {"op": "add", "args": ["x", "three"]},
        })
        self.assertEqual(self.program.run(["out"])["out"]["value"], 5)

    def snapshot(self):
        return self.program.export_bridge(
            since=self.session.count, execution_since=self.session.execution_count,
            outputs=["out"], include_environment=False)

    def test_real_suffix_is_proved_once_and_warm_reuse_checks_no_new_module(self):
        accepted = self.session.certify(self.snapshot())
        self.assertEqual(accepted["new_rows"], 3)
        self.assertEqual(accepted["new_value_proofs"], 3)
        self.assertEqual(accepted["new_modules"], 1)
        self.assertEqual(accepted["lean_processes"], 1)
        self.assertEqual(self.session.count, 3)
        self.assertEqual(self.session.execution_count, 3)
        source = (self.directory / (self.session.module + ".lean")).read_text()
        self.assertIn("delta_checked", source)
        self.assertIn("Pipeline.certify_extension IncrementalReceipt0.certified", source)
        files = sorted(path.name for path in self.directory.iterdir())
        processes = self.session.lean_processes
        warm = self.session.certify(self.snapshot())
        self.assertEqual(warm["new_rows"], 0)
        self.assertEqual(warm["new_value_proofs"], 0)
        self.assertEqual(warm["new_modules"], 0)
        self.assertEqual(warm["lean_processes"], 0)
        self.assertEqual(self.session.lean_processes, processes)
        self.assertEqual(sorted(path.name for path in self.directory.iterdir()), files)

    def test_input_change_reuses_compiler_theorem_but_proves_new_actual_values(self):
        self.session.certify(self.snapshot())
        previous = self.session.module
        self.program.edit("x", {"op": "input", "value": 7})
        self.assertEqual(self.program.run(["out"])["out"]["executed"], 10)
        result = self.session.certify(self.snapshot())
        self.assertEqual(result["new_rows"], 0)
        self.assertEqual(result["new_value_proofs"], 2)
        self.assertEqual(result["new_modules"], 1)
        self.assertEqual(self.session.count, 3)
        self.assertEqual(self.session.execution_count, 5)
        source = (self.directory / (self.session.module + ".lean")).read_text()
        self.assertNotIn("delta_checked", source)
        self.assertIn(":= " + previous + ".certified", source)
        self.assertIn("Evaluation.add_correct", source)
        self.assertIn(previous + ".value_", source)

    def test_coherent_wrong_opcode_is_rejected_by_lean_without_advancing_prefix(self):
        original = self.snapshot()
        forged = copy.deepcopy(original)
        row = next(row for row in forged["rows"] if row["operation"]["op"] == "add")
        row["code"][-1] = ["MUL"]
        row["artifact"]["code"] = copy.deepcopy(row["code"])
        rehash_compiler_suffix(forged)
        with self.assertRaisesRegex(KernelError, "Lean rejected"):
            self.session.certify(forged)
        self.assertEqual(self.session.count, 0)
        self.assertEqual(self.session.execution_count, 0)
        self.assertEqual(self.session.certify(original)["new_rows"], 3)

    def test_direct_scope_change_then_edit_rebinds_all_parents_before_kernel_extension(self):
        self.session.certify(self.snapshot())
        implementation = copy.deepcopy(self.engine.scope["implementation"])
        revisions = (
            (True, {"op": "mul", "args": ["x", "three"]}, 6),
            (1.0, {"op": "mul", "args": ["x", "three"]}, 6),
            ("new-contract", {"op": "add", "args": ["x", "x"]}, 4),
        )
        for label, definition, expected in revisions:
            with self.subTest(scope=type(label).__name__):
                before = copy.deepcopy(self.program.artifacts)
                scope = copy.deepcopy(self.engine.scope)
                scope["qualification"] = {"label": label}
                if isinstance(label, str):
                    scope.pop("implementation")
                self.engine.set_scope(scope)
                history = self.engine.path.read_bytes()
                with self.assertRaisesRegex(ValueError, "cyclic"):
                    self.program.edit("out", {"op": "add", "args": ["out", "x"]})
                self.assertEqual(self.engine.path.read_bytes(), history)
                self.assertEqual(self.program.artifacts, before)
                planned = self.program.edit("out", definition)
                self.assertEqual(planned["planned"], 3)
                self.assertEqual(self.engine.scope["implementation"], implementation)
                for name, bundle in self.program.artifacts.items():
                    for stage, node in bundle.items():
                        self.assertNotEqual(node, before[name][stage])
                        self.assertEqual(canonical(self.engine.tasks[node].scope),
                                         canonical(self.engine.scope))
                self.assertEqual(self.program.run(["out", "three"])["out"]["executed"], expected)
                accepted = self.session.certify(self.snapshot())
                self.assertEqual(accepted["new_rows"], 3)
                self.assertEqual(accepted["new_value_proofs"], 3)
                self.assertEqual(accepted["new_modules"], 1)
                self.assertEqual(self.session.certify(self.snapshot())["new_modules"], 0)

    def test_coherent_missing_joint_premise_is_rejected_by_lean(self):
        forged = copy.deepcopy(self.snapshot())
        row = next(row for row in forged["rows"] if row["operation"]["op"] == "add")
        row["premises"].pop()
        row["links"].pop()
        row["check_parents"].pop()
        row["artifact"]["links"] = list(row["links"])
        rehash_compiler_suffix(forged)
        # Isolate the compiler arity obligation from the separate value lane.
        forged.update(execution_start=0, execution_end=0,
                      execution_prefix="", execution_tail="", execution_rows=[],
                      observations={})
        with self.assertRaisesRegex(KernelError, "Lean rejected"):
            self.session.certify(forged)
        self.assertEqual(self.session.count, 0)

    def test_wrong_cursor_and_divergent_journal_prefix_are_refused(self):
        self.session.certify(self.snapshot())
        valid = self.snapshot()
        wrong_cursor = copy.deepcopy(valid)
        wrong_cursor["start"] -= 1
        with self.assertRaisesRegex(KernelError, "prefix"):
            self.session.certify(wrong_cursor)
        divergent = copy.deepcopy(valid)
        divergent["prefix"] = "0" * 64
        with self.assertRaisesRegex(KernelError, "prefix"):
            self.session.certify(divergent)
        self.assertEqual(self.session.count, 3)
        self.assertEqual(self.session.execution_count, 3)
        self.assertEqual(self.session.certify(valid)["new_modules"], 0)

    def test_historical_receipt_cannot_be_called_current_in_a_different_scope(self):
        self.session.certify(self.snapshot())
        forged = copy.deepcopy(self.snapshot())
        forged["scope"] = {**forged["scope"], "toolchain": "different-current-toolchain"}
        with self.assertRaisesRegex(KernelError, "historical|active scope"):
            self.session.certify(forged)
        self.assertEqual(self.session.count, 3)

    def test_retained_observations_reject_bool_and_float_scope_relabeling(self):
        revised = copy.deepcopy(self.engine.scope)
        revised["qualification"] = {"label": 1}
        self.program.change_scope(revised)
        self.program.run(["out"])
        self.session.certify(self.snapshot())
        valid = self.snapshot()
        before = (self.session.count, self.session.execution_count, self.session.lean_processes)
        for replacement in (True, 1.0):
            for relabel_observation in (False, True):
                with self.subTest(scope=type(replacement).__name__, observation=relabel_observation):
                    forged = copy.deepcopy(valid)
                    forged["scope"]["qualification"]["label"] = replacement
                    if relabel_observation:
                        forged["observations"]["out"]["scope"]["qualification"]["label"] = replacement
                    self.assertNotEqual(canonical(valid["scope"]), canonical(forged["scope"]))
                    with self.assertRaisesRegex(KernelError, "scope|identity"):
                        self.session.certify(forged)
                    self.assertEqual((self.session.count, self.session.execution_count,
                                      self.session.lean_processes), before)
        self.assertEqual(self.session.certify(valid)["new_modules"], 0)

    def test_matching_fabricated_observations_do_not_become_value_proofs(self):
        forged = copy.deepcopy(self.snapshot())
        forged["observations"]["out"]["value"] = 999
        forged["observations"]["out"]["executed"] = 999
        before = self.session.lean_processes
        with self.assertRaisesRegex(KernelError, "proven execution"):
            self.session.certify(forged)
        self.assertEqual(self.session.count, 0)
        self.assertEqual(self.session.execution_count, 0)
        self.assertEqual(self.session.lean_processes, before)

    def test_rehashed_fabricated_execution_is_rejected_by_kernel_arithmetic(self):
        forged = copy.deepcopy(self.snapshot())
        observed = forged["observations"]["out"]
        execution = next(row for row in forged["execution_rows"] if row["task"] == observed["execute_task"])
        execution["value"] = 999
        observed["value"] = observed["executed"] = 999
        rehash_execution_suffix(forged)
        with self.assertRaisesRegex(KernelError, "Lean rejected"):
            self.session.certify(forged)
        self.assertEqual(self.session.count, 0)
        self.assertEqual(self.session.execution_count, 0)

    def test_modified_imported_proof_object_is_rejected_on_restore(self):
        self.session.certify(self.snapshot())
        artifact = self.directory / (self.session.module + ".olean")
        artifact.write_bytes(artifact.read_bytes() + b"tampered")
        with self.assertRaisesRegex(KernelError, "integrity"):
            KernelSession(self.directory, lean=self.lean)

    def test_changed_fixed_proof_source_requires_a_new_session(self):
        self.session.certify(self.snapshot())
        sources = self.root / "changed-proof-source"
        sources.mkdir()
        original = Path(__file__).resolve().parent.parent / "proof"
        for name in ("Incremental", "Pipeline", "Evaluation"):
            shutil.copy2(original / (name + ".lean"), sources / (name + ".lean"))
        evaluation = sources / "Evaluation.lean"
        evaluation.write_text(evaluation.read_text() + "\n-- A distinct source version.\n")
        with self.assertRaisesRegex(KernelError, "scope changed"):
            KernelSession(self.directory, lean=self.lean, proof_root=sources)

    def test_rehashed_inconsistent_receipt_count_is_not_trusted(self):
        self.session.certify(self.snapshot())
        journal = self.directory / "receipts.jsonl"
        records = [json.loads(line) for line in journal.read_text().splitlines()]
        self.assertEqual(len(records), 1)
        receipt = records[0]
        receipt.pop("checksum")
        receipt["end"] = 999
        receipt["checksum"] = hashlib.sha256(canonical(receipt)).hexdigest()
        journal.write_bytes(canonical(receipt) + b"\n")
        with self.assertRaisesRegex(KernelError, "suffix length"):
            KernelSession(self.directory, lean=self.lean)

    def test_input_names_are_data_and_cannot_inject_lean_declarations(self):
        name = 'x"); axiom injected : False\n--'
        with make_engine(self.root / "quoted-name.jsonl") as engine:
            program = Program(engine, {name: {"op": "input", "value": 4},
                                       "out": {"op": "neg", "args": [name]}})
            self.assertEqual(program.run(["out"])["out"]["value"], -4)
            result = self.session.certify(program.export_bridge(outputs=["out"], include_environment=False))
        self.assertEqual(result["new_rows"], 2)
        self.assertEqual(result["new_value_proofs"], 2)
        self.assertLessEqual(set(result["axioms"]), {"propext", "Quot.sound"})
        source = (self.directory / (self.session.module + ".lean")).read_text()
        self.assertIn("Char.ofNat", source)
        self.assertNotIn("axiom injected", source)


if __name__ == "__main__":
    unittest.main()
