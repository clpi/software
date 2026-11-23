# Lane b: grain and provable returns for the witness hypergraph.
# Independent check on lane a's establishment. Three code paths, kept
# separate on purpose:
#   path one (extraction) reads the hypergraph alone and returns, for
#     each accounting entry address carried on a class node, the
#     candidate premise sets the hypergraph itself offers for that
#     entry: the full member set of its derivation link, the groups of
#     that set by environment, and the groups by environment and value
#     (the separations sections 17.3 and 17.4 name).
#   path two (check) loads the derivation record as oracle and, for
#     each entry, tests every candidate: (a) the candidate's witnesses
#     rendered as the record renders evidence, plus any source digest
#     elements, equal the recorded evidence as a set; (b) the four
#     parts re-derived from the candidate under section 17.3 equal
#     the recorded parts.
#   path three (refinement) loads the step file only for entries the
#     symbol grain left ambiguous or failing, and brings in the step
#     structure: which step named the entry in its changed list, and
#     which witnesses had arrived by that step.
# Run: python3 extract.py [workdir]
# Reads the hypergraph once; writes results.json beside this file.

import hashlib
import json
import re
import sys

base = "/home/hatch/workspace/traceability-scratch"
hpath = base + "/lane-a/hypergraph.json"
apath = base + "/snapshot/accounting.json"
spath = base + "/snapshot/steps.json"
out = (sys.argv[1] if len(sys.argv) > 1 else base + "/lane-b") + "/results.json"


def canon(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False)


def addr(value):
    return hashlib.sha256(canon(value).encode("utf-8")).hexdigest()


# ---------- path one: extraction, hypergraph only ----------

def show(wit):
    # the record's evidence rendering: batch :: source :: pin :: fact
    f = wit["fields"]
    return wit["time"][0]["batch"] + " :: " + f["source"] + " :: " + f["pin"] + " :: " + f["fact"]


def dig(wit):
    d = wit["fields"]["digests"]
    if not d:
        return None
    return "source digests: " + json.dumps(d, sort_keys=True)


def env(wit):
    # section 17.3 environment tiers one and two, per witness
    f = wit["fields"]
    if f["host"]:
        return f["host"]
    return "record: " + wit["time"][0]["batch"]


def extract(hg):
    nodes = {n["id"]: n for n in hg["nodes"]}
    deriv = {e["conclusion"]: e for e in hg["edges"] if e["kind"] == "derivation"}
    found = {}
    for node in hg["nodes"]:
        if node["kind"] != "class":
            continue
        f = node["fields"]
        members = [nodes[p] for p in deriv[node["id"]]["premises"]]
        groups = []
        seen = set()

        def add(group):
            key = frozenset(w["id"] for w in group)
            if key and key not in seen:
                seen.add(key)
                groups.append(sorted(group, key=lambda w: w["id"]))

        add(members)
        byenv = {}
        byboth = {}
        for w in members:
            byenv.setdefault(env(w), []).append(w)
            byboth.setdefault((env(w), w["fields"]["value"]), []).append(w)
        for group in byenv.values():
            add(group)
        for group in byboth.values():
            add(group)
        for entry in f["entries"]:
            found[entry] = {
                "class": f["label"],
                "project": f["project"],
                "fact": f["fact"],
                "candidates": groups,
            }
    return found


def rendered(candidate):
    out = set()
    for w in candidate:
        out.add(show(w))
        d = dig(w)
        if d:
            out.add(d)
    return out


# ---------- path two: check against the oracle ----------

span = re.compile(r"^\s*(\d+(?:\.\d+)?)\s*-\s*(\d+(?:\.\d+)?)\s*$")


def trim(text):
    # the record renders derived numbers in the six-significant-digit
    # general form (large byte counts appear in scientific notation)
    return format(float(text), "g")


def num(text):
    try:
        return float(text)
    except ValueError:
        return None


def parts(candidate, kind):
    # section 17.3 part derivation from a premise set
    if kind == "dependence":
        workload = "derived from the differing witnesses"
    else:
        contracts = sorted({w["fields"]["contract"] for w in candidate if w["fields"]["contract"]})
        if contracts:
            workload = " | ".join(contracts)
        else:
            batches = sorted({w["time"][0]["batch"] for w in candidate})
            workload = "procedure: " + " | ".join(batches)
    envs = sorted({env(w) for w in candidate})
    environment = envs[0] if len(envs) == 1 else "joined: " + " | ".join(envs)
    under = []
    if kind == "dependence":
        uncertainty = "the difference itself, as witnessed"
    else:
        ranges = set()
        for w in candidate:
            m = span.match(w["fields"]["range"] or "")
            if m:
                ranges.add((trim(m.group(1)), trim(m.group(2))))
        vals = [w["fields"]["value"] for w in candidate]
        if len(ranges) == 1:
            lo, hi = next(iter(ranges))
            uncertainty = "recorded range " + lo + " to " + hi
        elif len(ranges) > 1:
            uncertainty = "unresolvable: several recorded ranges"
        elif all(num(v) is not None for v in vals):
            if len(candidate) == 1:
                uncertainty = "underivable: single witness, no recorded range"
                under = ["uncertainty (single witness, no recorded range)"]
            else:
                nums = [num(v) for v in vals]
                lo = trim(str(vals[nums.index(min(nums))]))
                hi = trim(str(vals[nums.index(max(nums))]))
                uncertainty = "witnessed spread " + lo + " to " + hi + " over " + str(len(candidate)) + " witnesses"
        elif len(set(vals)) == 1:
            if len(candidate) == 1:
                uncertainty = "underivable: single witness, no recorded range"
                under = ["uncertainty (single witness, no recorded range)"]
            else:
                uncertainty = "agreement over " + str(len(candidate)) + " witnesses, no recorded spread"
        else:
            uncertainty = "unresolvable: differing non-numeric values, no recorded range"
    return {
        "workload": workload,
        "environment": environment,
        "uncertainty": uncertainty,
        "underivable": under,
    }


def passes(candidate, entry):
    # returns (evidence ok, parts ok, derived parts)
    ev = rendered(candidate) == set(entry["evidence"])
    got = parts(candidate, entry["kind"])
    want = {
        "workload": entry["workload"],
        "environment": entry["environment"],
        "uncertainty": entry["uncertainty"],
        "underivable": entry["underivable"],
    }
    return ev, got == want, got


# ---------- path three: refinement at derivation-step grain ----------

def refine(entry, cands, steps):
    # the step file names an entry in a changed list by this rendering
    tag = " | ".join([entry["project"], entry["fact"], entry["axis"], entry["environment"], entry["value"]])
    naming = [i for i, s in enumerate(steps) if any(c["entry"] == tag for c in s["changed"])]
    if not naming:
        return None, "no step names this entry in a changed list"
    last = max(naming)
    notes = []
    # finer candidates: premise groups cut to what had arrived by the
    # last step that named the entry (arrival read off witness time)
    finer = []
    seen = set()
    for cand in cands:
        cut = [w for w in cand if w["time"][0]["index"] <= last]
        key = frozenset(w["id"] for w in cut)
        if cut and key not in seen:
            seen.add(key)
            finer.append(cut)
    good = [c for c in finer if passes(c, entry)[0] and passes(c, entry)[1]]
    good = {frozenset(w["id"] for w in c): c for c in good}
    if len(good) == 1:
        return next(iter(good.values())), "arrival cut at step " + str(last) + " left one candidate"
    # value binding: the changed list names the entry by its value; the
    # candidate whose witnesses carry exactly that value is its premise
    bound = [c for c in good.values() if {w["fields"]["value"] for w in c} == {entry["value"]}]
    if len(bound) == 1:
        return bound[0], ("changed list at step " + str(last) + " (" + steps[last]["batch"] +
                          ") names the entry by its value, binding it to the witness carrying that value")
    notes.append("step grain left " + str(len(good)) + " candidates")
    return None, "; ".join(notes)


def main():
    with open(hpath, encoding="utf-8") as stream:
        hg = json.load(stream)
    found = extract(hg)
    with open(apath, encoding="utf-8") as stream:
        oracle = json.load(stream)["entries"]
    steps = None
    rows = []
    tally = {"symbol": 0, "step": 0, "failing": 0}
    for entry in oracle:
        a = addr(entry)
        info = found.get(a)
        row = {
            "entry": a,
            "class": entry["class"],
            "project": entry["project"],
            "fact": entry["fact"],
            "kind": entry["kind"],
        }
        if info is None:
            row["verdict"] = "failing"
            row["reason"] = "entry address not carried on any class node"
            tally["failing"] += 1
            rows.append(row)
            continue
        good = []
        seen = set()
        for cand in info["candidates"]:
            ev, ok, _ = passes(cand, entry)
            if ev and ok:
                key = frozenset(w["id"] for w in cand)
                if key not in seen:
                    seen.add(key)
                    good.append(cand)
        if len(good) == 1:
            row["verdict"] = "exact at symbol grain"
            row["premises"] = sorted(w["id"] for w in good[0])
            tally["symbol"] += 1
        else:
            if steps is None:
                with open(spath, encoding="utf-8") as stream:
                    steps = json.load(stream)["steps"]
            picked, note = refine(entry, info["candidates"], steps)
            if picked is not None:
                row["verdict"] = "exact at step grain"
                row["premises"] = sorted(w["id"] for w in picked)
                if len(good) == 0:
                    row["reason"] = "symbol grain: no candidate reproduced the entry; refinement: " + note
                else:
                    row["reason"] = ("symbol grain: " + str(len(good)) +
                                     " distinct premise sets reproduce the rendered evidence and parts, "
                                     "so the set is not separated at symbol grain; refinement: " + note)
                tally["step"] += 1
            else:
                row["verdict"] = "failing"
                if len(good) == 0:
                    row["reason"] = "no candidate premise set passes the evidence and parts checks; " + note
                else:
                    row["reason"] = (str(len(good)) + " distinct premise sets pass both checks and step grain "
                                     "does not separate them; " + note)
                tally["failing"] += 1
        rows.append(row)
    rows.sort(key=lambda r: r["entry"])
    with open(out, "w", encoding="utf-8") as stream:
        json.dump({"totals": tally, "checked": len(rows), "entries": rows}, stream, indent=1, sort_keys=True)
        stream.write("\n")
    print(json.dumps({"checked": len(rows), "totals": tally}))


if __name__ == "__main__":
    main()
