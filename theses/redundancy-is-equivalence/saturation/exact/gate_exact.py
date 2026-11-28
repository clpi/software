"""Gates at the finest grain. Truth for a row is the composed exact
decider's verdict, checked against Z3 alone wherever both decide.
For every engine and corpus: joins, false joins (joined, but different
at the finest grain), rows decided exactly, rows left undecided, time
and peak memory. Writes results/exact/summary.json.
Usage: python3 exact/gate_exact.py RESULTS_DIR
"""
import gzip, json, os, sys


def jl(p):
    rows, summ = [], {}
    for l in open(p):
        r = json.loads(l)
        if r.get("summary"):
            summ = r
        else:
            rows.append(r)
    return rows, summ


def wsat(d, c):
    p = os.path.join(d, f"{c}.json")
    f = open(p) if os.path.exists(p) else gzip.open(p + ".gz", "rt")
    return json.load(f)


def main(d):
    out, gates = {"corpora": {}}, []

    def gate(n, ok, det):
        gates.append((n, bool(ok), det))

    for c in ("real", "suites", "cross"):
        xr, xs = jl(os.path.join(d, "exact", f"{c}_xdecide.jsonl"))
        zr, zs = jl(os.path.join(d, "exact", f"{c}_z3.jsonl"))
        er, es = jl(os.path.join(d, "exact", f"{c}_egg.jsonl"))
        ew = json.load(open(os.path.join(d, "exact", f"{c}_egg.wall")))["wall_s"]
        truth = {r["id"]: r["verdict"] for r in xr}
        zt = {r["id"]: r["verdict"] for r in zr}
        dis = [i for i in truth if truth[i] in ("equal", "differ") and zt[i] in ("equal", "differ") and truth[i] != zt[i]]
        gate(f"{c}: composed decider and Z3 alone never disagree", not dis, f"{len(dis)} disagreements")
        gate(f"{c}: composed decider decides every row", all(v != "unknown" for v in truth.values()),
             f"{sum(v == 'unknown' for v in truth.values())} unknown")
        eng = {}

        def score(name, verdicts, wall, mem):
            joins = sum(1 for i, v in verdicts.items() if v == "equal")
            false = sum(1 for i, v in verdicts.items() if v == "equal" and truth[i] == "differ")
            exact = sum(1 for i, v in verdicts.items() if v == truth[i] and v != "unknown")
            eng[name] = {"joins": joins, "false_joins": false, "decided_exactly": exact,
                         "undecided": len(truth) - exact - false, "wall_s": wall, "vmhwm_kb": mem}

        score("composed exact", truth, xs["wall_s"], xs["vmhwm_kb"])
        score("z3 alone", zt, zs["wall_s"], zs["vmhwm_kb"])
        score("egg", {r["id"]: ("equal" if r["status"] == "proved" else "unknown") for r in er}, ew, es["vmhwm_kb"])
        W = wsat(d, c)
        for e in ("decide", "witness", "saturate_beh", "greedy", "saturate", "sat_bound"):
            if e not in W:
                continue
            v = W[e]
            m = {"agree": "equal", "proved": "equal", "refuted": "differ"}
            score(e, {r["id"]: m.get(r["status"], "unknown") for r in v["rows"]}, v["wall_s"], v["vmhwm_kb"])
        out["corpora"][c] = {"rows": len(truth), "equal": sum(v == "equal" for v in truth.values()), "engines": eng}
        x = eng["composed exact"]
        for n, s in eng.items():
            if n == "composed exact":
                continue
            gate(f"{c}: composed exact makes no false join and decides at least as many rows as {n}",
                 x["false_joins"] == 0 and x["decided_exactly"] >= s["decided_exactly"],
                 f"{x['decided_exactly']} vs {s['decided_exactly']} decided; {n} false joins {s['false_joins']}")
            if x["wall_s"] > s["wall_s"] or x["vmhwm_kb"] > s["vmhwm_kb"]:
                out.setdefault("losses", []).append(
                    f"{c}: {n} faster or smaller ({s['wall_s']} s, {s['vmhwm_kb']} KB vs {x['wall_s']} s, {x['vmhwm_kb']} KB)")
    rare = [r for r in jl(os.path.join(d, "exact", "suites_xdecide.jsonl"))[0] if r["suite"] == "rare"]
    gate("rare differences: refuted at the finest grain", all(r["verdict"] == "differ" for r in rare), f"{len(rare)} rows")
    out["gates"] = [{"gate": g, "pass": ok, "detail": det} for g, ok, det in gates]
    json.dump(out, open(os.path.join(d, "exact", "summary.json"), "w"), indent=1)
    ok = True
    for g, p, det in gates:
        ok &= p
        print("PASS" if p else "FAIL", g, "|", det)
    for c, v in out["corpora"].items():
        for n, s in v["engines"].items():
            print("TABLE", c, n, s)
    for l in out.get("losses", []):
        print("LOSS", l)
    print("ALL PASS" if ok else "GATE FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1]))
