"""Replay the complete incremental pipeline and its standing attack suite.

All generated proof modules, compiled artifacts, journals, and cold comparison
runs live in a fresh temporary directory outside the repository. Retained
transcripts may be redirected with INCREMENTAL_RECEIPTS_DIR so a published pin
can be rechecked without changing its committed measurements.
"""
from __future__ import annotations

import contextlib
import hashlib
import io
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent.parent
STAGES = ("recompute", "compile", "certificate", "check", "execute")
EXPECTED_TESTS = 42
EXPECTED_STEPS = (
    ("cold", 2097152, (23, 23, 23, 23, 23), 23, 23, 1),
    ("warm", 2097152, (0, 0, 0, 0, 0), 0, 0, 0),
    ("input_edit", 3145728, (21, 0, 0, 0, 21), 0, 21, 1),
    ("structural_edit", -1572864, (11, 11, 11, 11, 11), 11, 11, 1),
    ("revert", 2097152, (0, 0, 0, 0, 0), 0, 0, 0),
    ("restart", 2097152, (0, 0, 0, 0, 0), 0, 0, 0),
    ("scope_change", 2097152, (23, 23, 23, 23, 23), 23, 23, 1),
)


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def validate_campaign(report):
    require(report["depth"] == 20, "campaign depth changed")
    require(len(report["steps"]) == len(EXPECTED_STEPS), "campaign transaction coverage changed")
    for actual, (name, value, stages, rows, values, modules) in zip(report["steps"], EXPECTED_STEPS):
        require(actual["step"] == name, f"wrong campaign transaction: {actual['step']}")
        require(actual["values"] == {"d20": value, "side_out": -7}, f"wrong observed values in {name}")
        expected_stages = {stage: count for stage, count in zip(STAGES, stages) if count}
        require(actual["delta"]["executed"] == expected_stages, f"unexpected incremental stage work in {name}")
        require(actual["new_compiler_rows"] == rows, f"wrong compiler suffix length in {name}")
        require(actual["delta"]["hot_history_scans"] == 0, f"hot journal scan in {name}")
        require(not actual["delta"]["failures_this_session"], f"unaccounted failed callback in {name}")
        kernel = actual["kernel"]
        require(kernel is not None, "the campaign must run the real Lean kernel")
        require(kernel["new_rows"] == rows and kernel["new_value_proofs"] == values,
                f"unexpected kernel compiler/value proof work in {name}")
        require(kernel["new_modules"] == modules and kernel["lean_processes"] == modules,
                f"unexpected kernel receipt module/process work in {name}")
        require(set(kernel["axioms"]) <= {"propext", "Quot.sound"}, f"axiom budget exceeded in {name}")
        require(actual["cold_executed"] == {stage: 23 for stage in STAGES},
                f"fresh cold comparison did not execute all stages in {name}")
        cold_kernel = actual["cold_kernel"]
        require(cold_kernel["new_rows"] == 23 and cold_kernel["new_value_proofs"] == 23
                and cold_kernel["new_modules"] == 1 and cold_kernel["lean_processes"] == 1,
                f"fresh cold comparison did not independently kernel-check all artifacts/values in {name}")
        if name in ("warm", "restart"):
            require(actual["delta"]["events"] == 0, f"no-op transaction wrote history in {name}")
        if name == "input_edit":
            require(actual["delta"]["source_validation_visits"] == 0,
                    "input value edit unnecessarily revalidated source topology")
        if name == "revert":
            require(actual["delta"]["tasks"] == 0 and actual["delta"]["events"] == 1,
                    "revert must reuse historical nodes and append one head transaction")
        if name == "restart":
            require(actual["restart"]["replayed_events"] > 0
                    and actual["restart"]["kernel_replayed_receipts"] == 3
                    and actual["restart"]["kernel_new_lean_processes"] == 0,
                    "restart receipt replay or reuse changed")
    expected_total = {"recompute": 78, "compile": 57, "certificate": 57, "check": 57, "execute": 78}
    require(report["cumulative_incremental"]["executed"] == expected_total, "wrong cumulative incremental work")
    require(report["cumulative_cold_executed"] == {stage: 161 for stage in STAGES}, "wrong cumulative actual cold work")
    require(report["kernel_cumulative"]["total_rows"] == 57
            and report["kernel_cumulative"]["total_value_proofs"] == 78
            and report["kernel_cumulative"]["total_receipts"] == 4,
            "wrong cumulative kernel proof inventory")
    require(report["kernel_cold_new_rows"] == 161 and report["kernel_cold_new_modules"] == 7
            and report["kernel_cold_receipt_processes"] == 7,
            "wrong cumulative actual cold kernel work")
    sessions = report["kernel_prior_sessions"] + [report["kernel_cumulative"]]
    require(sum(session["fixed_modules_built_this_session"] for session in sessions) == 4,
            "fixed/bootstrap proof compilation was not reused across restart")
    require(sum(session["lean_processes_this_session"] for session in sessions) == 8,
            "unexpected total kernel processes including fixed/bootstrap work")
    require(report["diamond"]["stored_source_nodes_in_main_diamond"] == 21
            and report["diamond"]["expanded_tree_nodes"] == 2097151, "diamond representation changed")
    family = report["cartesian_family"]
    require(family["represented_distinct_tuples"] == 1048576 and family["materialized_tuples"] == 0,
            "factored family representation/output distinction changed")
    require(family["metrics"]["executed"] == {**{stage: 2 for stage in STAGES}, "factor": 1},
            "factored family executed unexpected component work")
    require(family["kernel"]["new_rows"] == 2 and family["kernel"]["new_value_proofs"] == 2,
            "factored component alternatives lack independent kernel checks")


def main():
    configured = os.environ.get("INCREMENTAL_RECEIPTS_DIR")
    receipts = Path(configured).resolve() if configured else ROOT / "proof" / "receipts"
    receipts.mkdir(parents=True, exist_ok=True)
    lines = []

    def emit(line):
        lines.append(line)
        print(line, flush=True)

    try:
        lean = shutil.which(os.environ.get("LEAN", "lean"))
        require(lean is not None, "Lean executable not found; set LEAN to the pinned executable")
        version = subprocess.run([lean, "--version"], capture_output=True, text=True, check=True).stdout.strip()
        pin = (ROOT / "proof" / "lean-toolchain").read_text().strip()
        match = re.fullmatch(r"leanprover/lean4:v([0-9.]+)", pin)
        require(match is not None and f"version {match.group(1)}," in version,
                "Lean executable does not match proof/lean-toolchain")
        emit(version)
        emit(f"Incremental receipt directory: {receipts}")
        fixture_dir = ROOT / "examples" / "incremental" / "receipts"
        expected_names = [f"IncrementalReceipt{index}.lean" for index in range(5)]
        require(sorted(path.name for path in fixture_dir.glob("*.lean")) == expected_names,
                "expected five committed incremental receipt fixtures")
        with tempfile.TemporaryDirectory(prefix="traceability-incremental-gate-", dir="/tmp") as temporary:
            temporary = Path(temporary)
            unit_temporary = temporary / "unit-temporary"
            unit_temporary.mkdir()
            env = {**os.environ, "LEAN": lean, "TMPDIR": str(unit_temporary),
                   "PYTHONDONTWRITEBYTECODE": "1"}
            command = [sys.executable, "-m", "unittest", "discover", "-s", "incremental", "-t", ".", "-v"]
            tests = subprocess.run(command, cwd=ROOT, env=env, stdout=subprocess.PIPE,
                                   stderr=subprocess.STDOUT, text=True)
            (receipts / "incremental-tests.log").write_text(version + "\nCommand: " + " ".join(command) + "\n\n" + tests.stdout)
            require(tests.returncode == 0, "incremental test suite failed; see incremental-tests.log")
            counted = re.search(r"^Ran (\d+) tests in (.+)$", tests.stdout, re.M)
            require(counted is not None and int(counted.group(1)) == EXPECTED_TESTS,
                    "incremental test coverage changed or tests did not complete")
            passed = re.findall(r"^test\S+ \(.+\) \.\.\. ok$", tests.stdout, re.M)
            require(len(passed) == EXPECTED_TESTS and re.search(r"^OK$", tests.stdout, re.M),
                    f"all {EXPECTED_TESTS} named tests must pass without skips")
            emit(f"Incremental tests: {EXPECTED_TESTS}/{EXPECTED_TESTS} passed; OK")
            emit(f"Full named test transcript: {receipts / 'incremental-tests.log'}")
            from .demo import campaign
            campaign_output = io.StringIO()
            run_dir = temporary / "campaign"
            with contextlib.redirect_stdout(campaign_output):
                report = campaign(run_dir, depth=20, lean=lean)
            (receipts / "incremental-campaign-console.log").write_text(campaign_output.getvalue())
            (receipts / "incremental-campaign.json").write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
            validate_campaign(report)
            for name in expected_names:
                expected = (fixture_dir / name).read_bytes()
                actual = (run_dir / "kernel" / name).read_bytes()
                require(actual == expected,
                        f"regenerated {name} differs: expected {hashlib.sha256(expected).hexdigest()}, got {hashlib.sha256(actual).hexdigest()}")
            emit("Deterministic proof fixtures: 5/5 regenerated modules byte-identical")
            for step in report["steps"]:
                stages = " ".join(f"{stage}={step['delta']['executed'].get(stage, 0)}" for stage in STAGES)
                kernel = step["kernel"]
                emit(f"{step['step']}: {stages}; Lean rows={kernel['new_rows']} values={kernel['new_value_proofs']} modules={kernel['new_modules']}; d20={step['values']['d20']} side_out=-7")
            emit("Cumulative incremental: recompute=78 compile=57 certificate=57 check=57 execute=78")
            emit("Cumulative actual cold rebuilds: 161 successful invocations per stage across seven fresh rebuilds")
            emit("Kernel cumulative: 57 compiler rows, 78 value proofs, 4 new receipt modules; 4 fixed/bootstrap modules built once, 8 total Lean processes")
            emit("Kernel actual cold rebuilds: 161 compiler rows, 161 value proofs, 7 new receipt modules across seven fresh sessions")
            emit("Kernel restart: 3 retained receipts replayed, 0 new Lean processes")
            emit("Factored family: 1,048,576 represented independent tuples; 0 tuples materialized; 2 compiled and kernel-checked alternatives")
            emit(f"Full measured campaign: {receipts / 'incremental-campaign.json'}")
            emit("Incremental pipeline gate: PASS")
        status = 0
    except (RuntimeError, OSError, ValueError, KeyError, subprocess.SubprocessError) as error:
        emit(f"Incremental pipeline gate: FAIL — {error}")
        status = 1
    (receipts / "incremental-gate.log").write_text("\n".join(lines) + "\n")
    return status


if __name__ == "__main__":
    sys.exit(main())
