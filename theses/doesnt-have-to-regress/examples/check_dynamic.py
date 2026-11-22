#!/usr/bin/env python3
"""Independent adversarial controls for the compiled dynamic adapter.

The Lean theorems cover finite semantic inputs. These controls additionally
exercise parsing, complete profile extraction, event identity, archival state,
and the adapter's composition of recertification, selection, and undo.
"""

from __future__ import annotations

import copy
import json
from pathlib import Path
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[1]
BINARY = ROOT / ".lake" / "build" / "bin" / "dynamic"
EXAMPLES = ROOT / "examples"
CASES = 0


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def run_text(name: str, source: str, *, reject: bool = False,
             error_contains: str | None = None) -> list[dict]:
    global CASES
    CASES += 1
    with tempfile.TemporaryDirectory(prefix="dynamic-controls-") as directory:
        path = Path(directory) / "scenario.json"
        path.write_text(source)
        result = subprocess.run(
            [str(BINARY), str(path)], text=True, capture_output=True, timeout=15,
            cwd=ROOT, check=False,
        )
    if reject:
        require(result.returncode != 0, f"{name}: invalid input was accepted")
        require(not result.stdout.strip(), f"{name}: invalid scenario published a trace")
        require(bool(result.stderr.strip()), f"{name}: refusal had no explanation")
        if error_contains:
            require(error_contains in result.stderr,
                    f"{name}: wrong refusal: {result.stderr.strip()}")
        return []
    require(result.returncode == 0,
            f"{name}: executable failed: {result.stderr.strip()}")
    require(not result.stderr.strip(), f"{name}: unexpected stderr: {result.stderr}")
    rows = [json.loads(line) for line in result.stdout.splitlines()]
    require(bool(rows), f"{name}: no trace")
    verify_trace(name, rows)
    return rows


def run(name: str, scenario: dict, **options) -> list[dict]:
    rows = run_text(name, json.dumps(scenario), **options)
    if not options.get("reject", False):
        require(len(rows) == len(scenario["commands"]) + 1,
                f"{name}: missing or extra command reports")
        require([row["op"] for row in rows] ==
                ["initialize"] + [command["op"] for command in scenario["commands"]],
                f"{name}: report order differs from command order")
    return rows


def verify_trace(name: str, rows: list[dict]) -> None:
    naturals = ["context", "incumbent", "archive", "observations", "journal_events",
                "evidence_entries", "evaluated", "reused", "total_evaluated", "total_reused"]
    state_fields = ["context", "incumbent", "archive", "observations", "journal_events",
                    "evidence_entries", "total_evaluated", "total_reused"]
    evaluated = reused = 0
    previous = None
    for index, row in enumerate(rows):
        label = f"{name}, report {index}"
        require(type(row.get("accepted")) is bool, f"{label}: accepted is not Boolean")
        require(isinstance(row.get("op"), str) and isinstance(row.get("status"), str),
                f"{label}: missing operation or status")
        for key in naturals:
            require(type(row.get(key)) is int and row[key] >= 0,
                    f"{label}: {key} is not a natural number")
        evaluated += row["evaluated"]
        reused += row["reused"]
        require(row["total_evaluated"] == evaluated and row["total_reused"] == reused,
                f"{label}: work totals do not match the actual report prefix")
        require(row["evidence_entries"] == evaluated,
                f"{label}: receipt archive growth differs from new leaf evaluations")
        if previous:
            for key in ["archive", "observations", "journal_events", "evidence_entries"]:
                require(row[key] >= previous[key], f"{label}: {key} history shrank")
            if row["status"] in ["replayed", "conflict-refused"]:
                require(row["evaluated"] == row["reused"] == 0,
                        f"{label}: replay or conflict did new work")
                require(all(row[key] == previous[key] for key in state_fields),
                        f"{label}: replay or conflict mutated state")
            if row["op"] == "query":
                require(all(row[key] == previous[key] for key in
                            ["context", "incumbent", "archive", "observations", "journal_events"]),
                        f"{label}: read-only query published state")
        previous = row


def project(rows: list[dict], field: str) -> list:
    return [row[field] for row in rows]


def fixture(name: str) -> tuple[dict, list[dict]]:
    scenario = json.loads((EXAMPLES / name).read_text())
    return scenario, run(name, scenario)


def contract(keys: list[int] | None = None) -> dict:
    keys = [0] if keys is None else keys
    return {"context": 0, "keys": keys,
            "cells": [{"key": key, "required": [0], "allowed": [0, 1]} for key in keys]}


def release(identifier: int = 0, cost: tuple[int, int] = (2, 2),
            *, offered: list[int] | None = None, possible: list[int] | None = None,
            context: int = 0) -> dict:
    return {"id": identifier, "context": context,
            "cells": [{"key": 0, "offered": [0] if offered is None else offered,
                       "possible": [0] if possible is None else possible, "cost": list(cost)}]}


def scenario(commands: list[dict] | None = None) -> dict:
    return {"contract": contract(), "initial": release(), "commands": commands or []}


def check_fixtures() -> None:
    _, stream = fixture("dynamic-stream.json")
    require(project(stream, "status") == [
        "certified", "permitted", "permitted", "permitted", "selected", "unchanged",
        "unchanged", "adopted", "refused", "refused", "replayed", "conflict-refused",
        "refused", "reobserved", "refused", "unchanged", "replayed"],
        "dynamic stream: wrong admission, undo, replay, or context decision")
    require(project(stream, "incumbent") ==
            [0, 0, 0, 0, 1, 1, 1, 3, 3, 3, 3, 3, 3, 2, 2, 2, 2],
            "dynamic stream: wrong selected release")
    require(project(stream, "journal_events") ==
            [0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 6, 6, 7, 8, 9, 10, 10],
            "dynamic stream: event identity did not preserve journal counts")
    require(project(stream, "context") == [0] * 13 + [1] * 4,
            "dynamic stream: context changed outside its explicit epoch event")
    require([(row["evaluated"], row["reused"]) for row in stream[:4]] ==
            [(4, 3), (0, 7), (1, 6), (0, 7)],
            "dynamic stream: cold, warm, cost-only, or replay work is wrong")
    require(all(not stream[index]["accepted"] for index in [8, 9, 10, 11, 12, 14]),
            "dynamic stream: a new promise or protected cost was bypassed")
    require(stream[13]["evaluated"] > 0,
            "dynamic stream: context event reused every stale context receipt")

    _, reversible = fixture("dynamic-reversible.json")
    require(project(reversible, "incumbent") == [0, 1, 0, 0, 0, 1, 0, 1],
            "reversible stream: inverse or inverse-of-inverse selected wrong artifact")
    require(project(reversible, "status") == [
        "certified", "adopted", "accepted", "replayed", "conflict-refused",
        "accepted", "accepted", "accepted"], "reversible stream: wrong undo decisions")
    require(project(reversible, "journal_events") == [0, 1, 2, 2, 2, 3, 4, 5],
            "reversible stream: undo overwrote history or replay duplicated it")
    require(all(row["evaluated"] == 0 for row in reversible[2:]),
            "reversible stream: exact archived proofs were unnecessarily recomputed")

    _, scope = fixture("dynamic-scope.json")
    require(project(scope, "incumbent") == [0, 0, 1, 1, 1, 1],
            "scope change failed to reconsider a formerly tied archived candidate")
    require(project(scope, "status") ==
            ["certified", "unchanged", "adopted", "permitted", "permitted", "refused"],
            "scope change: wrong admission or scope-erasure decision")
    require([(row["evaluated"], row["reused"]) for row in scope[:5]] ==
            [(4, 3), (0, 21), (5, 74), (1, 11), (0, 12)],
            "scope change: new-key, full rescan, or replay work differs")

    _, refusal = fixture("dynamic-contract-refusal-greedy.json")
    require(project(refusal, "status") ==
            ["certified", "refused-selected", "unchanged", "unchanged", "permitted"] and
            project(refusal, "incumbent") == [0, 1, 1, 1, 1],
            "refused contract proposal stranded its retained old-contract improvement")
    require(not refusal[1]["accepted"] and refusal[-1]["accepted"],
            "refused contract proposal was installed or its old contract was lost")

    invalid = sorted(EXAMPLES.glob("dynamic-invalid-*.json"))
    require(len(invalid) >= 10, "missing standing invalid dynamic fixtures")
    for path in invalid:
        run_text(path.name, path.read_text(), reject=True)


def check_semantic_mutations() -> None:
    for name, candidate in [
        ("cached-capability-failure", release(1, offered=[])),
        ("cached-envelope-failure", release(1, possible=[2])),
    ]:
        rows = run(name, scenario([{"op": "query", "candidate": candidate}] * 2))
        require(project(rows, "status") == ["certified", "refused", "refused"],
                f"{name}: invalid candidate became accepted")
        require([(row["evaluated"], row["reused"]) for row in rows[1:]] ==
                [(1, 6), (0, 7)], f"{name}: negative evidence was not safely reused")

    rows = run("candidate-context-is-an-input", scenario([
        {"op": "query", "candidate": release(1, context=1)},
    ]))
    require(rows[-1]["status"] == "refused" and rows[-1]["evaluated"] == 4,
            "candidate-context: stale context receipts were reused")

    # Contract adoption can fail while its proposed artifact improves the old
    # contract. Retaining it in the active archive must preserve maximality.
    next_contract = contract()
    next_contract["cells"][0]["required"] = [0, 1]
    base = scenario([
        {"op": "strengthen", "event": 1, "contract": next_contract,
         "candidate": release(1, (1, 1))},
        {"op": "arrive", "event": 2, "releases": [release(2, (2, 2))]},
        {"op": "query", "candidate": release(1, (1, 1))},
    ])
    rows = run("refused-adoption-still-reconsiders-retained-candidate", base)
    require(rows[1]["status"] == "refused-selected" and not rows[1]["accepted"],
            "refused adoption did not distinguish old-contract selection from new promises")
    require(project(rows, "incumbent") == [0, 1, 1, 1] and rows[-1]["accepted"],
            "refused adoption stranded a strict improvement or installed the failed promise")

    changed = contract()
    changed["context"] = 1
    rows = run("strengthening-cannot-smuggle-a-context-change", scenario([
        {"op": "strengthen", "event": 1, "contract": changed},
    ]))
    require(rows[-1]["status"] == "refused" and rows[-1]["context"] == 0,
            "strengthen silently rebased the comparison context")

    # An explicit context epoch establishes a new cost baseline for the same
    # incumbent. This is deliberately not a cross-context no-regression claim.
    rows = run("explicit-context-epoch-can-change-cost-baseline", scenario([
        {"op": "context", "event": 1, "context": 1, "initial": 0,
         "releases": [release(0, (200, 200), context=1)]},
    ]))
    require(rows[-1]["status"] == "reobserved" and rows[-1]["context"] == 1 and
            rows[-1]["incumbent"] == 0 and rows[-1]["evaluated"] == 4,
            "explicit context epoch did not establish and freshly certify its same-artifact baseline")


def check_input_boundaries() -> None:
    base = scenario()
    raw = json.dumps(base, separators=(",", ":"))
    for name, text in [
        ("trailing-garbage", raw + " extra"),
        ("duplicate-json-field", raw.replace('"context":0', '"context":0,"context":1', 1)),
        ("leading-zero-number", raw.replace('"context":0', '"context":00', 1)),
        ("negative-number", raw.replace('"context":0', '"context":-1', 1)),
        ("fractional-cost", raw.replace('"cost":[2,2]', '"cost":[1.5,2]')),
        ("trailing-array-comma", raw.replace('"keys":[0]', '"keys":[0,]')),
        ("malformed-json", raw[:-1]),
    ]:
        run_text(name, text, reject=True, error_contains="invalid dynamic scenario")

    mutations = []
    changed = copy.deepcopy(base)
    changed["accepted"] = True
    mutations.append(("untrusted-root-verdict", changed))
    changed = copy.deepcopy(base)
    changed["contract"]["stamp"] = 0
    mutations.append(("unbound-contract-stamp", changed))
    changed = copy.deepcopy(base)
    changed["initial"]["cells"][0]["cost"] = [2]
    mutations.append(("incomplete-cost-vector", changed))
    changed = copy.deepcopy(base)
    changed["commands"] = [{"op": "reconsider", "event": 1, "dirty": []}]
    mutations.append(("caller-supplied-dirty-set", changed))
    changed = copy.deepcopy(base)
    changed["commands"] = [{"op": "arrive", "releases": []}]
    mutations.append(("missing-event-identity", changed))
    for name, value in mutations:
        run(name, value, reject=True, error_contains="invalid dynamic scenario")

    mutations = []
    changed = copy.deepcopy(base)
    changed["contract"]["keys"] = []
    changed["contract"]["cells"] = []
    mutations.append(("empty-protected-scope", changed, "no protected keys"))
    changed = copy.deepcopy(base)
    changed["contract"]["keys"] = [0, 0]
    mutations.append(("duplicate-protected-key", changed, "duplicate protected key"))
    changed = copy.deepcopy(base)
    changed["contract"]["cells"] *= 2
    mutations.append(("duplicate-contract-cell", changed, "duplicate contract cell"))
    changed = copy.deepcopy(base)
    changed["contract"]["cells"] = []
    mutations.append(("missing-contract-cell", changed, "missing a protected-key cell"))
    changed = copy.deepcopy(base)
    changed["contract"]["cells"].append({"key": 1, "required": [], "allowed": []})
    mutations.append(("undeclared-contract-cell", changed, "undeclared-key cell"))
    changed = copy.deepcopy(base)
    changed["initial"]["cells"][0]["possible"] = [2]
    mutations.append(("invalid-baseline-envelope", changed, "initial release is not certified"))
    for name, value, reason in mutations:
        run(name, value, reject=True, error_contains=reason)

    run("same-id-different-profile", scenario([
        {"op": "query", "candidate": release(0, (1, 1))},
    ]), reject=True, error_contains="already bound to different data")
    run("duplicate-arrival-identifiers", scenario([
        {"op": "arrive", "event": 1, "releases": [release(1), release(1)]},
    ]), reject=True, error_contains="duplicate release identifier")
    run("query-does-not-register-rollback-target", scenario([
        {"op": "query", "candidate": release(1)},
        {"op": "rollback", "event": 1, "release": 1},
    ]), reject=True, error_contains="not in the current archive")
    run("context-cannot-introduce-unarchived-artifact", scenario([
        {"op": "context", "event": 1, "context": 1, "initial": 0,
         "releases": [release(0, context=1), release(1, context=1)]},
    ]), reject=True, error_contains="unarchived artifact")
    run("context-must-change-label", scenario([
        {"op": "context", "event": 1, "context": 0, "initial": 0,
         "releases": [release()]},
    ]), reject=True, error_contains="must establish a new context")
    run("context-row-must-match-new-label", scenario([
        {"op": "context", "event": 1, "context": 1, "initial": 0,
         "releases": [release()]},
    ]), reject=True, error_contains="wrong context")


def main() -> None:
    require(BINARY.is_file(), f"build the dynamic executable first: {BINARY}")
    check_fixtures()
    check_semantic_mutations()
    check_input_boundaries()
    print(f"DYNAMIC_CONTROLS_PASS cases={CASES}")


if __name__ == "__main__":
    main()
