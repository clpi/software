"""End-to-end positive and semantic-mutation tests for the reference compiler."""
import copy
import tempfile
import unittest

from .engine import Context, Dependency, Task, difference
from .pipeline import Program, make_engine, cold_oracle, _check


class PipelineTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.path = self.temporary.name + "/history.jsonl"
        self.engine = make_engine(self.path)
        self.addCleanup(self.temporary.cleanup)
        self.addCleanup(lambda: self.engine.close() if not self.engine._stream.closed else None)

    def program(self):
        return Program(self.engine, {
            "x": {"op": "input", "value": 4},
            "three": {"op": "const", "value": 3},
            "sum": {"op": "add", "args": ["x", "three"]},
            "square": {"op": "mul", "args": ["sum", "sum"]},
            "negative": {"op": "neg", "args": ["square"]},
            "side": {"op": "const", "value": 100},
        })

    def test_all_opcodes_execute_and_only_input_value_cone_recomputes(self):
        program = self.program()
        self.assertEqual(program.run(["negative", "side"])["negative"]["value"], -49)
        prior = copy.deepcopy(program.artifacts)
        before = program.metrics()
        cursor = program.export_bridge()["end"]
        program.edit("x", {"op": "input", "value": 5})
        outputs = program.run(["negative", "side"])
        self.assertEqual(outputs["negative"]["executed"], -64)
        self.assertEqual({name: value["value"] for name, value in outputs.items()},
                         cold_oracle(program.definitions, ["negative", "side"]))
        delta = difference(program.metrics(), before)
        self.assertEqual(delta["executed"], {"recompute": 4, "execute": 4})
        self.assertEqual(delta["source_validation_visits"], 0)
        self.assertEqual(delta["source_nodes_planned"], 4)
        self.assertEqual(program.artifacts["side"], prior["side"])
        for name in prior:
            for stage in ("compile", "certificate", "check"):
                self.assertEqual(program.artifacts[name][stage], prior[name][stage])
        self.assertEqual(program.export_bridge(cursor, include_environment=False)["rows"], [])

    def test_structural_edit_and_revert_reuse_historical_proof_nodes(self):
        program = self.program()
        original = program.run(["negative", "side"])
        prior = copy.deepcopy(program.artifacts)
        before = program.metrics()
        program.edit("square", {"op": "add", "args": ["sum", "sum"]})
        changed = program.run(["negative", "side"])
        self.assertEqual(changed["negative"]["value"], -14)
        self.assertEqual(difference(program.metrics(), before)["executed"],
                         {stage: 2 for stage in ("recompute", "compile", "certificate", "check", "execute")})
        before = program.metrics()
        program.edit("square", {"op": "mul", "args": ["sum", "sum"]})
        self.assertEqual(program.run(["negative", "side"]), original)
        self.assertEqual(difference(program.metrics(), before)["executed"], {})
        self.assertEqual(program.artifacts, prior)
        self.assertEqual(difference(program.metrics(), before)["tasks"], 0)
        self.assertEqual(difference(program.metrics(), before)["events"], 1)

    def test_restart_replays_once_and_restores_every_result(self):
        program = self.program()
        expected = program.run(["negative", "side"])
        count = len(self.engine.tasks)
        self.engine.close()
        self.engine = make_engine(self.path)
        restored = Program(self.engine)
        before = restored.metrics()
        self.assertGreater(before["replay_events"], 0)
        self.assertEqual(restored.run(["negative", "side"]), expected)
        self.assertEqual(len(self.engine.tasks), count)
        self.assertEqual(difference(restored.metrics(), before)["executed"], {})
        self.assertEqual(difference(restored.metrics(), before)["events"], 0)

    def test_export_preserves_order_multiplicity_and_append_only_row_indices(self):
        program = self.program()
        program.run(["negative"])
        initial = program.export_bridge(outputs=["negative"])
        square_row = next(row for row in initial["rows"] if row["operation"]["op"] == "mul")
        self.assertEqual(square_row["premises"][0], square_row["premises"][1])
        for row in initial["rows"]:
            self.assertTrue(all(dep < row["id"] for dep in row["premises"]))
        program.edit("sum", {"op": "mul", "args": ["x", "three"]})
        program.run(["negative"])
        suffix = program.export_bridge(initial["end"], include_environment=False)
        self.assertEqual([row["id"] for row in suffix["rows"]], list(range(initial["end"], suffix["end"])))
        self.assertIsNone(suffix["environment"])
        self.assertEqual(suffix["observations"], {})
        prefix_again = program.export_bridge()["rows"][:initial["end"]]
        self.assertEqual(prefix_again, initial["rows"])

    def checker_context(self, program, name):
        task = self.engine.tasks[program.artifacts[name]["check"]]
        dependencies = tuple(Dependency(self.engine.tasks[node], copy.deepcopy(self.engine.results[node])) for node in task.deps)
        return Context(task, dependencies)

    def test_checker_rejects_forged_trace(self):
        program = self.program()
        program.run(["negative"])
        context = self.checker_context(program, "sum")
        context.dependencies[1].value["trace"][-1] = [["literal", 999]]
        with self.assertRaisesRegex(ValueError, "transition"):
            _check(context)

    def test_checker_rejects_coherent_certificate_for_wrong_compiled_operation(self):
        program = self.program()
        program.run(["negative"])
        context = self.checker_context(program, "sum")
        context.dependencies[0].value["code"][-1] = ["MUL"]
        certificate = context.dependencies[1].value
        certificate["block"]["code"][-1] = ["MUL"]
        certificate["trace"][-1] = [["mul", ["argument", 0], ["argument", 1]]]
        with self.assertRaisesRegex(ValueError, "specified operation"):
            _check(context)

    def test_hot_leaf_edit_does_not_iterate_the_active_source_tables(self):
        program = self.program()
        program.run(["negative", "side"])

        class LookupOnly(dict):
            def __iter__(self):
                raise AssertionError("hot edit scanned whole source/index table")
            def items(self):
                raise AssertionError("hot edit copied whole source/index table")
            def keys(self):
                raise AssertionError("hot edit scanned whole source/index table")
            def values(self):
                raise AssertionError("hot edit scanned whole source/index table")

        program.definitions = LookupOnly(program.definitions)
        program.dependents = LookupOnly(program.dependents)
        program.artifacts = LookupOnly(program.artifacts)
        program.edit("x", {"op": "input", "value": 9})
        self.assertEqual(program.run(["negative"])["negative"]["value"], -144)
        self.assertEqual(program.export_bridge(0, outputs=["negative"], include_environment=False)["environment"], None)

    def test_factored_product_is_compact_and_does_not_claim_enumerated_outputs(self):
        program = Program(self.engine, {"zero": {"op": "const", "value": 0}, "one": {"op": "const", "value": 1}})
        choices = {f"coordinate{index}": ["zero", "one"] for index in range(20)}
        family = program.factor_product(choices)
        self.assertEqual(family["choice_assignments"], 2 ** 20)
        self.assertEqual(family["materialized_tuples"], 0)
        self.assertEqual(len(family["factors"]), 20)
        self.assertEqual(self.engine.executed["compile"], 2)
        self.assertEqual(self.engine.executed["check"], 2)
        before = self.engine.metrics()
        self.assertEqual(program.factor_product(choices), family)
        self.assertEqual(difference(self.engine.metrics(), before)["executed"], {})
        self.assertEqual(difference(self.engine.metrics(), before)["events"], 0)

    def test_deterministic_edit_campaign_matches_fresh_checked_pipeline(self):
        program = self.program()
        outputs = ["negative", "side"]
        for index in range(8):
            program.edit("x", {"op": "input", "value": index - 4})
            program.edit("sum", {"op": "mul" if index % 2 else "add", "args": ["x", "three"]})
            actual = program.run(outputs)
            expected = cold_oracle(program.definitions, outputs)
            self.assertEqual({name: actual[name]["value"] for name in outputs}, expected)
            with tempfile.TemporaryDirectory() as fresh:
                with make_engine(fresh + "/cold.jsonl") as engine:
                    cold = Program(engine, program.definitions).run(outputs)
                    self.assertEqual({name: cold[name]["executed"] for name in outputs}, expected)

    def test_deep_reversed_chain_accepts_valid_edits_and_still_refuses_cycles(self):
        depth = 1100
        definitions = {
            f"n{index}": ({"op": "input", "value": 7} if index == 0
                          else {"op": "neg", "args": [f"n{index - 1}"]})
            for index in range(depth, -1, -1)
        }
        output = f"n{depth}"
        self.assertEqual(next(iter(definitions)), output)
        program = Program(self.engine, definitions)
        result = program.run([output])
        self.assertEqual(result[output]["value"], 7)
        self.assertEqual(result[output]["executed"], 7)
        self.assertEqual(cold_oracle(program.definitions, [output]), {output: 7})

        # Changing the root's prerequisite list forces another deep validation.
        program.edit(output, {"op": "add", "args": [f"n{depth - 1}", f"n{depth - 2}"]})
        result = program.run([output])
        self.assertEqual(result[output]["value"], 0)
        self.assertEqual(result[output]["executed"], 0)
        self.assertEqual(cold_oracle(program.definitions, [output]), {output: 0})

        before = self.engine.metrics()["events"]
        with self.assertRaisesRegex(ValueError, "cyclic"):
            program.edit("n0", {"op": "neg", "args": [output]})
        self.assertEqual(program.definitions["n0"], {"op": "input", "value": 7})
        self.assertEqual(self.engine.metrics()["events"], before)
        self.assertEqual(program.run([output])[output]["executed"], 0)
        cyclic = dict(program.definitions)
        cyclic["n0"] = {"op": "neg", "args": [output]}
        with self.assertRaisesRegex(ValueError, "cyclic"):
            cold_oracle(cyclic, [output])


if __name__ == "__main__":
    unittest.main()
