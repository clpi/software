"""Measured cumulative reuse campaign; never enumerates an exponential output set."""
from __future__ import annotations

import argparse
from collections import Counter
import json
from pathlib import Path
import time

from .engine import clone, difference
from .pipeline import Program, make_engine, cold_oracle


def write_json(path: Path, value):
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")


def campaign(directory: Path, depth: int = 20, lean: str | None = None):
    if depth < 2:
        raise ValueError("diamond depth must be at least two")
    directory.mkdir(parents=True, exist_ok=True)
    journal = directory / "history.jsonl"
    if journal.exists():
        raise ValueError("use a fresh output directory; the demonstration never truncates history")
    if lean:
        from .lean import KernelSession
        kernel = KernelSession(directory / "kernel", lean=lean)
    else:
        kernel = None
    prior_kernel_sessions = []
    engine = make_engine(journal)
    program = Program(engine)
    definitions = {"d0": {"op": "input", "value": 2},
                   "side": {"op": "input", "value": 7},
                   "side_out": {"op": "neg", "args": ["side"]}}
    for index in range(1, depth + 1):
        definitions[f"d{index}"] = {"op": "add", "args": [f"d{index - 1}", f"d{index - 1}"]}
    outputs = [f"d{depth}", "side_out"]
    middle = max(1, depth // 2)
    steps, cursor, execution_cursor = [], 0, 0
    cold_total = Counter()
    cold_work = Counter()
    cold_kernel_rows = cold_kernel_modules = cold_kernel_processes = 0

    def record(label, action, startup=None):
        nonlocal cursor, execution_cursor, cold_kernel_rows, cold_kernel_modules, cold_kernel_processes
        before = program.metrics()
        start = time.perf_counter()
        action()
        result = program.run(outputs)
        expected = cold_oracle(program.definitions, outputs)
        if {name: value["value"] for name, value in result.items()} != expected:
            raise AssertionError("incremental result disagrees with independent cold oracle")
        bridge = program.export_bridge(cursor, outputs=outputs, include_environment=False,
                                       execution_since=execution_cursor)
        write_json(directory / f"bridge-{label}.json", bridge)
        kernel_receipt = kernel.certify(bridge) if kernel else None
        cursor, execution_cursor = bridge["end"], bridge["execution_end"]
        elapsed = time.perf_counter() - start
        delta = difference(program.metrics(), before)
        cold_start = time.perf_counter()
        with make_engine(directory / f"cold-{label}.jsonl", scope=engine.scope) as fresh:
            cold = Program(fresh, program.definitions)
            cold_result = cold.run(outputs)
            if {name: value["executed"] for name, value in cold_result.items()} != expected:
                raise AssertionError("fresh checked compiler result disagrees with cold oracle")
            cold_metrics = cold.metrics()
            cold_total.update(cold_metrics["executed"])
            cold_work.update(cold_metrics["work"])
            cold_kernel = None
            if lean:
                fresh_kernel = KernelSession(directory / f"cold-kernel-{label}", lean=lean)
                cold_kernel = fresh_kernel.certify(cold.export_bridge(outputs=outputs, include_environment=False))
                cold_kernel_rows += cold_kernel["new_rows"]
                cold_kernel_modules += cold_kernel["new_modules"]
                cold_kernel_processes += cold_kernel["lean_processes"]
        item = {"step": label, "values": expected, "delta": delta,
                "seconds": elapsed, "cold_seconds": time.perf_counter() - cold_start,
                "cold_executed": cold_metrics["executed"], "cold_work": cold_metrics["work"],
                "new_compiler_rows": len(bridge["rows"]), "compiler_prefix_rows": bridge["end"],
                "kernel": kernel_receipt, "cold_kernel": cold_kernel,
                "affected_source_nodes": list(program.last_affected)}
        if startup:
            item["restart"] = startup
        steps.append(item)
        print(json.dumps({"step": label, "executed": delta["executed"],
                          "new_compiler_rows": len(bridge["rows"]),
                          "kernel_new_modules": kernel_receipt["new_modules"] if kernel_receipt else None,
                          "kernel_new_value_proofs": kernel_receipt["new_value_proofs"] if kernel_receipt else None,
                          "values": expected}, sort_keys=True), flush=True)

    record("cold", lambda: program.apply(definitions))
    record("warm", lambda: program.apply(definitions))
    record("input_edit", lambda: program.edit("d0", {"op": "input", "value": 3}))
    record("structural_edit", lambda: program.edit(f"d{middle}", {"op": "neg", "args": [f"d{middle - 1}"]}))
    record("revert", lambda: program.apply({"d0": definitions["d0"], f"d{middle}": definitions[f"d{middle}"]}))
    engine.close()
    restart_start = time.perf_counter()
    engine = make_engine(journal)
    program = Program(engine)
    startup = {"seconds": time.perf_counter() - restart_start, "replayed_events": engine.replay_events,
               "scope": "one explicit restart replay; excluded from the following hot-operation delta"}
    if kernel:
        prior_kernel_sessions.append(kernel.metrics())
        kernel_restart_start = time.perf_counter()
        kernel = KernelSession(directory / "kernel", lean=lean)
        startup.update({"kernel_seconds": time.perf_counter() - kernel_restart_start,
                        "kernel_replayed_receipts": kernel.metrics()["replayed_receipts"],
                        "kernel_new_lean_processes": kernel.metrics()["lean_processes_this_session"]})
    record("restart", lambda: None, startup=startup)
    revised_scope = clone(engine.scope)
    revised_scope["qualification_profile"] = "second-complete-scope"
    record("scope_change", lambda: program.change_scope(revised_scope))

    with make_engine(directory / "factors.jsonl") as factor_engine:
        factors = Program(factor_engine, {"zero": {"op": "const", "value": 0}, "one": {"op": "const", "value": 1}})
        family = factors.factor_product({f"coordinate{index}": ["zero", "one"] for index in range(depth)})
        factor_metrics = factors.metrics()
        factor_kernel = None
        if lean:
            factor_session = KernelSession(directory / "factor-kernel", lean=lean)
            factor_kernel = factor_session.certify(factors.export_bridge(include_environment=False))
        write_json(directory / "factored-family.json", family)

    report = {"contract": "finite pure exact-integer reference compiler; no production Idol integration",
              "depth": depth, "steps": steps,
              "cumulative_incremental": engine.metrics(),
              "cumulative_cold_executed": dict(cold_total), "cumulative_cold_work": dict(cold_work),
              "kernel_cumulative": kernel.metrics() if kernel else None,
              "kernel_prior_sessions": prior_kernel_sessions,
              "kernel_cold_new_rows": cold_kernel_rows, "kernel_cold_new_modules": cold_kernel_modules,
              "kernel_cold_receipt_processes": cold_kernel_processes,
              "diamond": {"stored_source_nodes_in_main_diamond": depth + 1,
                          "expanded_tree_nodes": 2 ** (depth + 1) - 1,
                          "expanded_tree_nodes_are": "constructed count; no expanded tree was executed or allocated",
                          "local_proofs": "DAG nodes referencing parent proof IDs, never copied subproof trees"},
              "cartesian_family": {"manifest": family, "metrics": factor_metrics, "kernel": factor_kernel,
                                   "represented_distinct_tuples": 2 ** depth,
                                   "materialized_tuples": 0,
                                   "qualification": "independent tuple coordinates choosing distinct constants 0 or 1; no cross-coordinate constraints"},
              "measurement_limits": [
                  "executed counts successful completed stage invocations; attempted and failed callback counts are separately recorded per process",
                  "work is instrumented local stage operation units, not CPU cycles or a bound on arbitrary-precision arithmetic or JSON serialization",
                  "seconds are measured wall time including persistence and optional kernel checks; no universal wall-time speedup is claimed",
                  "compiler correspondence proofs and captured-input value proofs are separately incrementally checked by Lean; Python check receipts are not kernel receipts",
                  "warm/no-op operations perform key/index/receipt checks even when zero new stage work and zero new journal records are reported",
                  "revert appends a current-head update while reusing prior tasks/results; append-only history never erases obsolete contracts",
                  "journal replay is linear at restart and reported explicitly; hot source updates visit changed dependency cones without scanning history",
                  "generic runner purity and complete dependency declarations, single-writer local journal ownership, and physical storage integrity remain assumptions",
                  "an exponential number of distinct demanded outputs still requires proportional materialization; factoring does not execute them for free"]}
    write_json(directory / "REPORT.json", report)
    write_json(directory / "final-bridge.json", program.export_bridge(outputs=outputs))
    engine.close()
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--depth", type=int, default=20)
    parser.add_argument("--lean", help="enable the independent incremental Lean receipt pipeline")
    args = parser.parse_args()
    report = campaign(args.output, args.depth, args.lean)
    print(json.dumps({"report": str(args.output / "REPORT.json"),
                      "incremental_executed": report["cumulative_incremental"]["executed"],
                      "cold_executed": report["cumulative_cold_executed"],
                      "represented_tuple_choices": report["cartesian_family"]["represented_distinct_tuples"],
                      "materialized_tuples": 0}, sort_keys=True))


if __name__ == "__main__":
    main()
