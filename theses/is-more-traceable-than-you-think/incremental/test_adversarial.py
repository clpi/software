"""Standing adversarial controls for full-key append-only computation."""
import copy
from pathlib import Path
import tempfile
import unittest

from .engine import Engine, Result, canonical, difference
from .pipeline import Program, make_engine


class EngineAttacks(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.path = Path(self.temporary.name) / "history.jsonl"
        self.instances = []
        self.addCleanup(self.close_engines)

    def close_engines(self):
        for engine in self.instances:
            if not engine._stream.closed:
                engine.close()

    def engine(self, runners, scope=None, **kwargs):
        engine = Engine(self.path, scope or {"source": "v1", "toolchain": "v1"}, runners, **kwargs)
        self.instances.append(engine)
        return engine

    @staticmethod
    def leaf(context):
        return Result(context.task.payload["value"])

    def test_all_premises_are_required_before_a_parent_is_published(self):
        available = {"second": False}
        parents_run = []

        def leaf(context):
            if context.task.payload.get("second") and not available["second"]:
                raise ValueError("second premise is unavailable")
            return context.task.payload["value"]

        def joint(context):
            parents_run.append(tuple(dep.value for dep in context.dependencies))
            return sum(dep.value for dep in context.dependencies)

        engine = self.engine({"leaf": leaf, "joint": joint})
        first = engine.intern("leaf", {"value": 2})
        second = engine.intern("leaf", {"value": 3, "second": True})
        parent = engine.intern("joint", {}, [first, second])
        with self.assertRaisesRegex(ValueError, "unavailable"):
            engine.demand([parent])
        self.assertEqual(engine.results, {first: 2})
        self.assertEqual(parents_run, [])
        available["second"] = True
        self.assertEqual(engine.demand([parent]), [5])
        self.assertEqual(parents_run, [(2, 3)])
        self.assertEqual(engine.executed["joint"], 1)

    def test_forward_and_self_references_cannot_bootstrap_a_cycle(self):
        engine = self.engine({"leaf": self.leaf})
        for dep in (0, 1, 999):
            with self.assertRaises(ValueError):
                engine.intern("leaf", {"value": 2}, [dep])
        self.assertEqual(engine.tasks, [])
        leaf = engine.intern("leaf", {"value": 2})
        with self.assertRaises(ValueError):
            engine.intern("leaf", {"value": 3}, [len(engine.tasks)])
        self.assertEqual(engine.demand([leaf]), [2])

    def test_ordered_arguments_and_repeated_positions_are_not_set_union(self):
        engine = self.engine({
            "leaf": self.leaf,
            "sub": lambda c: c.dependencies[0].value - c.dependencies[1].value,
            "sum": lambda c: sum(d.value for d in c.dependencies),
        })
        two = engine.intern("leaf", {"value": 2})
        three = engine.intern("leaf", {"value": 3})
        forward = engine.intern("sub", {}, [two, three])
        reverse = engine.intern("sub", {}, [three, two])
        twice = engine.intern("sum", {}, [two, two])
        self.assertEqual(engine.demand([forward, reverse, twice]), [-1, 1, 4])
        self.assertNotEqual(forward, reverse)
        self.assertEqual(engine.tasks[twice].deps, (two, two))
        self.assertEqual(engine.executed["leaf"], 2)

    def test_every_scope_coordinate_participates_in_cache_identity(self):
        baseline = {"source": 0, "environment": 0, "contract": 0, "toolchain": 0,
                    "checker": 0, "recipe": 0, "payload": 0, "implementation": 0}
        engine = self.engine({"leaf": self.leaf, "other": self.leaf}, baseline)
        original = engine.intern("leaf", {"value": 2})
        identities = {original}
        for coordinate in baseline:
            revised = {**baseline, coordinate: 1}
            engine.set_scope(revised)
            node = engine.intern("leaf", {"value": 2})
            self.assertNotIn(node, identities, coordinate)
            identities.add(node)
            self.assertEqual(engine.demand([node]), [2])
        engine.set_scope(baseline)
        self.assertEqual(engine.intern("leaf", {"value": 2}), original)
        self.assertNotIn(engine.intern("other", {"value": 2}), identities)

    def test_unresolved_historical_task_cannot_run_with_a_new_scope(self):
        engine = self.engine({"leaf": self.leaf})
        old = engine.intern("leaf", {"value": 2})
        engine.set_scope({"source": "v1", "toolchain": "v2"})
        with self.assertRaisesRegex(ValueError, "historical"):
            engine.demand([old])
        self.assertNotIn(old, engine.results)
        current = engine.intern("leaf", {"value": 2})
        self.assertNotEqual(old, current)
        self.assertEqual(engine.demand([current]), [2])
        engine.set_scope({"source": "v1", "toolchain": "v1"})
        self.assertEqual(engine.demand([old, current]), [2, 2])

    def test_superseding_current_binding_does_not_erase_old_history(self):
        engine = self.engine({"leaf": self.leaf})
        old = engine.intern("leaf", {"value": 2})
        engine.bind("head", old)
        self.assertEqual(engine.demand([old]), [2])
        prefix = self.path.read_bytes()
        new = engine.intern("leaf", {"value": 3})
        engine.bind("head", new)
        self.assertEqual(engine.demand([new, old]), [3, 2])
        self.assertEqual(engine.bindings["head"], new)
        self.assertTrue(self.path.read_bytes().startswith(prefix))
        self.assertEqual(engine.results[old], 2)
        before = engine.metrics()
        engine.bind("head", new)
        self.assertEqual(difference(engine.metrics(), before)["events"], 0)
        retained = self.path.read_bytes()
        for invalid in (True, float(new), False, float(old), -1, len(engine.tasks)):
            with self.subTest(binding=invalid, binding_type=type(invalid).__name__):
                with self.assertRaisesRegex(ValueError, "unknown task"):
                    engine.commit_update({"pending": {"value": 99}}, {"head": invalid})
                self.assertEqual(self.path.read_bytes(), retained)
                self.assertEqual(engine.bindings["head"], new)
                self.assertIs(type(engine.bindings["head"]), int)
                self.assertNotIn("pending", engine.sources)
        for value in (1, True, 1.0):
            before = engine.metrics()
            engine.commit_update({"identity": {"value": value}}, {"head": new})
            self.assertEqual(difference(engine.metrics(), before)["events"], 1)
            self.assertEqual(canonical(engine.sources["identity"]), canonical({"value": value}))
            before = engine.metrics()
            engine.commit_update({"identity": {"value": value}}, {"head": new})
            self.assertEqual(difference(engine.metrics(), before)["events"], 0)

    def test_forced_digest_collisions_do_not_alias_distinct_descriptors(self):
        engine = self.engine({"leaf": self.leaf, "sum": lambda c: sum(d.value for d in c.dependencies)},
                             digest=lambda _: "forced-collision")
        two = engine.intern("leaf", {"value": 2})
        three = engine.intern("leaf", {"value": 3})
        parent = engine.intern("sum", {}, [two, three])
        self.assertNotEqual(two, three)
        self.assertEqual(engine.intern("leaf", {"value": 2}), two)
        self.assertEqual(engine.demand([two, three, parent]), [2, 3, 5])
        self.assertEqual(len(engine.buckets), 1)
        self.assertEqual(len(engine.tasks), 3)

    def test_shared_diamond_uses_one_completed_invocation_per_distinct_node(self):
        calls = []

        def runner(context):
            calls.append(context.task.id)
            return sum(dep.value for dep in context.dependencies) if context.dependencies else 1

        engine = self.engine({"node": runner})
        root = engine.intern("node", {"level": 0})
        depth = 18
        for level in range(1, depth + 1):
            root = engine.intern("node", {"level": level}, [root, root])
        self.assertEqual(engine.demand([root]), [2 ** depth])
        self.assertEqual(len(calls), depth + 1)
        self.assertEqual(len(set(calls)), depth + 1)
        self.assertEqual(len(engine.results), depth + 1)
        self.assertGreater(2 ** (depth + 1) - 1, len(calls))
        before = engine.metrics()
        self.assertEqual(engine.demand([root, root]), [2 ** depth, 2 ** depth])
        self.assertEqual(len(calls), depth + 1)
        delta = difference(engine.metrics(), before)
        self.assertEqual(delta["executed"], {})
        self.assertEqual(delta["events"], 0)

    def test_distinct_binary_outputs_still_require_distinct_materialized_nodes(self):
        def runner(context):
            if not context.dependencies:
                return 0
            return context.dependencies[0].value * 2 + context.task.payload["bit"]

        engine = self.engine({"node": runner})
        level = [engine.intern("node", {"root": True})]
        depth = 6
        for _ in range(depth):
            level = [engine.intern("node", {"bit": bit}, [parent])
                     for parent in level for bit in (0, 1)]
        values = engine.demand(level)
        self.assertEqual(values, list(range(2 ** depth)))
        self.assertEqual(len(set(values)), 2 ** depth)
        self.assertEqual(len(engine.tasks), 2 ** (depth + 1) - 1)
        self.assertEqual(engine.executed["node"], 127)

    def test_rejected_parent_publishes_no_success_and_failed_attempts_are_real_work(self):
        calls = []

        def reject(context):
            calls.append(context.task.id)
            raise ValueError("rejected parent")

        engine = self.engine({"leaf": self.leaf, "reject": reject})
        child = engine.intern("leaf", {"value": 2})
        parent = engine.intern("reject", {}, [child])
        for _ in range(2):
            with self.assertRaisesRegex(ValueError, "rejected parent"):
                engine.demand([parent])
        self.assertNotIn(parent, engine.results)
        self.assertEqual(engine.executed["leaf"], 1)
        self.assertEqual(engine.executed["reject"], 0)
        self.assertEqual(calls, [parent, parent])
        metrics = engine.metrics()
        self.assertEqual(metrics["attempts_this_session"]["reject"], 2)
        self.assertEqual(metrics["failures_this_session"]["reject"], 2)

    def test_runner_dependency_metadata_is_detached_from_authoritative_history(self):
        def mutate(context):
            dependency = context.dependencies[0]
            dependency.task.payload["nested"]["number"] = 999
            dependency.task.scope["toolchain"]["version"] = 999
            dependency.value["nested"]["number"] = 999
            context.task.scope["toolchain"]["version"] = 999
            return 0

        engine = self.engine({"leaf": lambda c: c.task.payload, "mutate": mutate},
                             {"toolchain": {"version": 1}})
        child = engine.intern("leaf", {"nested": {"number": 2}})
        parent = engine.intern("mutate", {}, [child])
        original = copy.deepcopy(engine.tasks[child].descriptor())
        self.assertEqual(engine.demand([parent]), [0])
        self.assertEqual(engine.tasks[child].descriptor(), original)
        self.assertEqual(engine.results[child], {"nested": {"number": 2}})
        self.assertEqual(engine.scope, {"toolchain": {"version": 1}})
        self.assertEqual(engine.tasks[parent].scope, engine.scope)

    def test_a_torn_journal_is_refused_without_truncating_history(self):
        runners = {"leaf": self.leaf}
        engine = self.engine(runners)
        node = engine.intern("leaf", {"value": 2})
        engine.demand([node])
        engine.close()
        with self.path.open("ab") as stream:
            stream.write(b'{"incomplete":')
        damaged = self.path.read_bytes()
        with self.assertRaisesRegex(ValueError, "truncated"):
            Engine(self.path, {"source": "v1", "toolchain": "v1"}, runners)
        self.assertEqual(self.path.read_bytes(), damaged)


class PipelineAttacks(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.path = Path(self.temporary.name) / "history.jsonl"
        self.engine = make_engine(self.path)
        self.addCleanup(lambda: self.engine.close() if not self.engine._stream.closed else None)

    def test_scope_identity_distinguishes_bool_int_and_float_across_current_views(self):
        baseline = {"qualification": {"label": 1}}
        definitions = {"out": {"op": "input", "value": 2}}

        def check_current(engine, program, previous, replacement):
            for stage, node in program.artifacts["out"].items():
                self.assertNotEqual(node, previous[stage])
                self.assertEqual(canonical(engine.tasks[node].scope), canonical(engine.scope))
                self.assertIs(type(engine.tasks[node].scope["qualification"]["label"]), type(replacement))
            self.assertIn(previous["check"], engine.results)

        for replacement in (True, 1.0):
            kind = type(replacement).__name__
            changed = {"qualification": {"label": replacement}}
            self.assertNotEqual(canonical(baseline), canonical(changed))
            with self.subTest(scope=kind, path="unresolved"):
                path = self.path.parent / f"identity-{kind}-unresolved.jsonl"
                with Engine(path, baseline, {"leaf": EngineAttacks.leaf}) as engine:
                    old = engine.intern("leaf", {"value": 2})
                    engine.set_scope(changed)
                    with self.assertRaisesRegex(ValueError, "historical"):
                        engine.demand([old])
                    self.assertNotIn(old, engine.results)
                    current = engine.intern("leaf", {"value": 2})
                    self.assertNotEqual(current, old)
                    self.assertEqual(engine.demand([current]), [2])
            for mode in ("change_scope", "run", "startup"):
                with self.subTest(scope=kind, path=mode):
                    path = self.path.parent / f"identity-{kind}-{mode}.jsonl"
                    with make_engine(path, scope=baseline) as engine:
                        program = Program(engine, definitions)
                        self.assertEqual(program.run(["out"])["out"]["value"], 2)
                        previous = copy.deepcopy(program.artifacts["out"])
                        revised = copy.deepcopy(engine.scope)
                        revised["qualification"]["label"] = replacement
                        if mode == "change_scope":
                            program.change_scope(revised)
                            check_current(engine, program, previous, replacement)
                            self.assertEqual(program.run(["out"])["out"]["executed"], 2)
                        elif mode == "run":
                            engine.set_scope(revised)
                            self.assertEqual(program.run(["out"])["out"]["executed"], 2)
                            check_current(engine, program, previous, replacement)
                    if mode == "startup":
                        with make_engine(path, scope=changed) as engine:
                            restored = Program(engine)
                            # Startup itself must rebind, before run can repair it.
                            check_current(engine, restored, previous, replacement)
                            self.assertEqual(restored.run(["out"])["out"]["executed"], 2)

    def test_input_change_reuses_all_symbolic_compilation_and_check_artifacts(self):
        program = Program(self.engine, {
            "a": {"op": "input", "value": 2},
            "b": {"op": "const", "value": 5},
            "minus": {"op": "const", "value": -5},
            "sum": {"op": "add", "args": ["a", "b"]},
            "out": {"op": "mul", "args": ["sum", "minus"]},
            "side": {"op": "const", "value": 99},
        })
        self.assertEqual(program.run(["out", "side"])["out"]["value"], -35)
        previous = copy.deepcopy(program.artifacts)
        before = program.metrics()
        program.edit("a", {"op": "input", "value": 7})
        self.assertEqual(program.run(["out", "side"])["out"]["executed"], -60)
        self.assertEqual(difference(program.metrics(), before)["executed"], {"recompute": 3, "execute": 3})
        self.assertEqual(program.artifacts["side"], previous["side"])
        for name, bundle in previous.items():
            for stage in ("compile", "certificate", "check"):
                self.assertEqual(program.artifacts[name][stage], bundle[stage])

    def test_structural_edit_changes_only_the_affected_local_artifact_family(self):
        program = Program(self.engine, {"a": {"op": "const", "value": 2},
                                       "b": {"op": "const", "value": 3},
                                       "out": {"op": "add", "args": ["a", "b"]}})
        self.assertEqual(program.run(["out"])["out"]["value"], 5)
        previous = copy.deepcopy(program.artifacts)
        before = program.metrics()
        program.edit("out", {"op": "mul", "args": ["a", "b"]})
        self.assertEqual(program.run(["out"])["out"]["value"], 6)
        for name in ("a", "b"):
            self.assertEqual(program.artifacts[name], previous[name])
        self.assertEqual(difference(program.metrics(), before)["executed"],
                         {stage: 1 for stage in ("recompute", "compile", "certificate", "check", "execute")})

    def test_cycle_and_missing_source_edits_do_not_publish_a_new_active_view(self):
        program = Program(self.engine, {"a": {"op": "const", "value": 2},
                                       "b": {"op": "const", "value": 3},
                                       "out": {"op": "add", "args": ["a", "b"]}})
        program.run(["out"])
        previous = copy.deepcopy(program.definitions)
        history = self.path.read_bytes()
        with self.assertRaises(ValueError):
            program.edit("a", {"op": "add", "args": ["out", "b"]})
        self.assertEqual(program.definitions, previous)
        self.assertEqual(self.path.read_bytes(), history)
        with self.assertRaises(ValueError):
            program.edit("out", {"op": "add", "args": ["missing", "b"]})
        self.assertEqual(program.definitions, previous)
        self.assertEqual(self.path.read_bytes(), history)

    def test_reopening_with_a_new_toolchain_rebinds_current_artifacts(self):
        program = Program(self.engine, {"a": {"op": "const", "value": 2},
                                       "b": {"op": "const", "value": 3},
                                       "out": {"op": "add", "args": ["a", "b"]}})
        self.assertEqual(program.run(["out"])["out"]["value"], 5)
        old = copy.deepcopy(program.artifacts)
        self.engine.close()
        self.engine = make_engine(self.path, scope={"toolchain": "new-toolchain"})
        restored = Program(self.engine)
        for name, bundle in restored.artifacts.items():
            self.assertNotEqual(bundle["compile"], old[name]["compile"])
            self.assertEqual(self.engine.tasks[bundle["compile"]].scope, self.engine.scope)
        before = restored.metrics()
        self.assertEqual(restored.run(["out"])["out"]["value"], 5)
        self.assertEqual(difference(restored.metrics(), before)["executed"],
                         {stage: 3 for stage in ("recompute", "compile", "certificate", "check", "execute")})
        self.assertIn(old["out"]["check"], self.engine.results)

    def test_bridge_uses_completion_indices_not_sparse_task_ids_or_intern_order(self):
        program = Program(self.engine, {"early": {"op": "const", "value": 9},
                                       "later": {"op": "const", "value": 2},
                                       "out": {"op": "add", "args": ["later", "later"]}})
        early = program.artifacts["early"]["compile"]
        later = program.artifacts["later"]["compile"]
        self.assertLess(early, later)
        self.assertEqual(program.run(["out"])["out"]["value"], 4)
        first = program.export_bridge(outputs=["out"])
        self.assertEqual([row["task"] for row in first["rows"]],
                         [later, program.artifacts["out"]["compile"]])
        self.assertEqual(first["rows"][1]["premises"], [0, 0])
        self.assertNotIn(early, self.engine.results)
        program.run(["early"])
        suffix = program.export_bridge(since=first["end"], include_environment=False)
        self.assertEqual([(row["id"], row["task"]) for row in suffix["rows"]], [(2, early)])
        self.assertEqual(program.export_bridge()["rows"][:2], first["rows"])


if __name__ == "__main__":
    unittest.main()
