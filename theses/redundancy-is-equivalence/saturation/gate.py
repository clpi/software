"""Gates over results/. Each gate states what it checks; a component
gate passes when turning the component off makes the result worse
(fewer joins found, or more fuel for the same joins) on the suite named.
Components with no measured benefit are reported as such and are not
gates. Also writes results/summary.json and results/summary.md.

Usage: python3 gate.py RESULTS_DIR
"""

import gzip
import json
import os
import statistics
import sys


def opener(path):
    if os.path.exists(path):
        return open(path)
    return gzip.open(path + ".gz", "rt")


def load(d, name):
    return json.load(opener(os.path.join(d, name)))


def proved(v, suite=None):
    return sum(1 for r in v["rows"] if r["status"] == "proved" and (suite is None or r["suite"].startswith(suite)))


def tot(v, f, suite=None):
    return sum(r[f] for r in v["rows"] if suite is None or r["suite"].startswith(suite))


def main(d):
    real, suites, gen = load(d, "real.json"), load(d, "suites.json"), load(d, "gen.json")
    dgen, dac = load(d, "divergence_gen.json"), load(d, "divergence_ac.json")
    out, gates = {}, []

    def gate(name, ok, detail):
        gates.append((name, bool(ok), detail))

    # soundness of every proof, every run
    allruns = [real, suites, gen, dgen, dac]
    unver = sum(1 for R in allruns for v in R.values() for r in v["rows"] if not r["verified"])
    gate("every proof re-verified on 64 fresh points", unver == 0, f"{unver} unverified")

    # the comparison table, inside the bound
    agree = {r["id"] for r in real["eval"]["rows"] if r["status"] == "agree"}
    table = []
    for e in ("witness", "greedy", "saturate", "saturate_beh", "sat_bound", "eval"):
        v = real[e]
        joins = len(agree) if e == "eval" else proved(v)
        table.append({"engine": e, "joins": joins, "alloc": tot(v, "alloc"), "match": tot(v, "match"),
                      "wall_s": v["wall_s"], "vmhwm_kb": v["vmhwm_kb"]})
    out["real_table"] = table
    out["real_rows"] = len(real["witness"]["rows"])
    out["real_agree"] = len(agree)

    w = real["witness"]
    sat_b = real["sat_bound"]
    gate("real: witness search finds every rule-derivable join saturation to the bound finds",
         {r["id"] for r in sat_b["rows"] if r["status"] == "proved"} <= {r["id"] for r in w["rows"] if r["status"] == "proved"},
         f"witness {proved(w)}, saturation to the bound {proved(sat_b)}")

    # components: real code and the suite that targets each
    comp = [
        ("hard behavioral falsification", "w_nobeh", real, None),
        ("anti-unification focus", "w_noau", real, None),
        ("AC multiset recognition", "w_nobag", suites, "ac"),
        ("linear-form recognition (added)", "w_nolin", real, None),
        ("bidirectional cones", "w_uni", real, None),
        ("bridge quota (80/20 beam)", "w_nobridge", suites, "valley"),
        ("provenance credit + UCB1", "w_nocredit", suites, None),
        ("merge dividend", "w_nodiv", suites, None),
        ("depth fuel", "w_nodepth", suites, None),
        ("entropy tiebreak", "w_noent", suites, None),
    ]
    comps = []
    for name, cfg, R, su in comp:
        on, off = R["witness"], R[cfg]
        pon, poff = proved(on, su), proved(off, su)
        fon, foff = tot(on, "match", su) + tot(on, "alloc", su), tot(off, "match", su) + tot(off, "alloc", su)
        better = pon > poff or (pon == poff and fon < foff)
        worse = pon < poff or (pon == poff and fon > foff)
        verdict = "helps" if better else ("hurts" if worse else "no effect")
        comps.append({"component": name, "suite": su or ("real" if R is real else "all suites"),
                      "joins_on": pon, "joins_off": poff, "fuel_on": fon, "fuel_off": foff, "verdict": verdict})
        if verdict == "helps":
            gate(f"component: {name}", True, f"on {pon} joins / {fon} fuel, off {poff} / {foff}")
    out["components"] = comps

    # divergence mechanisms
    sg, sn = dgen["sat_gen"], dgen["sat_nogen"]
    fix_n = sum(1 for r in sn["rows"] if r["status"] == "fixpoint")
    fix_g = sum(1 for r in sg["rows"] if r["status"] == "fixpoint")
    gate("generative rule: saturation stops reaching a fixpoint", fix_n > fix_g,
         f"fixpoints without the rule {fix_n}/{len(sn['rows'])}, with it {fix_g}/{len(sg['rows'])}; "
         f"nodes {tot(sn, 'enodes')} vs {tot(sg, 'enodes')}")
    wg = dgen["witness_gen"]
    alloc_cap = 400 + 2000  # budget plus dividend cap (fuelbound)
    gate("generative rule: witness search stays inside budget plus cap on every row",
         all(r["alloc"] <= alloc_cap for r in wg["rows"]), f"max alloc {max(r['alloc'] for r in wg['rows'])} <= {alloc_cap}")
    snm, wac, wnm = dac["sat_nomacro"], dac["witness"], dac["witness_nomacro"]
    gate("AC blowup: saturation without AC recognition exhausts on large sums; witness search proves all",
         proved(wac) == len(wac["rows"]) and proved(snm) < len(snm["rows"]),
         f"witness {proved(wac)}/{len(wac['rows'])} with {tot(wac, 'enodes')} nodes; "
         f"saturation {proved(snm)}/{len(snm['rows'])} with {tot(snm, 'enodes')} nodes; witness without recognition {proved(wnm)}")
    js, jw = suites["sat_bound"], suites["witness"]
    out["join"] = {"witness": [proved(jw, "join"), tot(jw, "match", "join")],
                   "saturate_bound": [proved(js, "join"), tot(js, "match", "join")]}
    naive, good = gen["w_naiveprov"], gen["witness"]
    gate("cycles: provenance stays acyclic with first-parent-min-depth; the naive arena does not",
         all(r["prov_acyclic"] for r in good["rows"]) and not all(r["prov_acyclic"] for r in naive["rows"]),
         f"design acyclic on {sum(r['prov_acyclic'] for r in good['rows'])}/{len(good['rows'])}; naive on {sum(r['prov_acyclic'] for r in naive['rows'])}")
    gate("no double credit with dedupe; the naive walk double-counts",
         tot(good, "double_credit") == 0 and tot(naive, "double_credit") > 0,
         f"{tot(good, 'double_credit')} vs {tot(naive, 'double_credit')}; walk steps {tot(good, 'walk_steps')} vs {tot(naive, 'walk_steps')}")
    # congruence credit reaches inner bridge rules
    cb = sum(r["cong_bridge_credit"] for R in (real, suites, gen) for r in R["witness"]["rows"] if r["cong_bridge_credit"] > 0)
    gate("congruence credit reaches an inner bridge rule", cb > 0, f"credit {cb:.3f} reached bridge rules through congruence")
    # memory bounded by fuel: at most one ProvNode per e-node touched
    bad = [r for R in (real, suites, gen) for r in R["witness"]["rows"] if r["prov_nodes"] > r["enodes"]]
    gate("per-epoch provenance at most one 16-byte node per e-node touched", not bad, f"{len(bad)} rows over")
    out["prov_bytes_max"] = max(r["prov_bytes"] for R in (real, suites, gen) for r in R["witness"]["rows"])

    # provenance overhead, same decisions
    ov = []
    for i in range(1, 6):
        p = os.path.join(d, f"overhead_{i}.json")
        if os.path.exists(p) or os.path.exists(p + ".gz"):
            o = json.load(opener(p))
            ov.append((o["prov"]["wall_s"], o["noprov"]["wall_s"],
                       sum(r["micros"] for r in o["prov"]["rows"]), sum(r["micros"] for r in o["noprov"]["rows"])))
            same = [a["status"] for a in o["prov"]["rows"]] == [b["status"] for b in o["noprov"]["rows"]]
            gate(f"overhead run {i}: identical decisions with and without provenance", same, "")
    if ov:
        out["overhead"] = {"prov_engine_us_median": statistics.median(x[2] for x in ov),
                           "noprov_engine_us_median": statistics.median(x[3] for x in ov)}

    out["gates"] = [{"gate": g, "pass": ok, "detail": det} for g, ok, det in gates]
    json.dump(out, open(os.path.join(d, "summary.json"), "w"), indent=1)
    ok_all = True
    for g, ok, det in gates:
        ok_all &= ok
        print(("PASS" if ok else "FAIL"), g, "|", det)
    for c in comps:
        print("COMPONENT", c["component"], c["suite"], c["verdict"], c)
    for t in table:
        print("TABLE", t)
    print("ALL PASS" if ok_all else "GATE FAILED")
    return 0 if ok_all else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1]))
