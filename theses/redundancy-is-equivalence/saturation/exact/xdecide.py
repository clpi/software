"""The composed exact decider, at the finest grain.

Stages, cheapest first, each one sound:
  1. identity: both sides hash-cons to one node (wsat --engine decide)
  2. refutation on the resolved points (64 per row, wsat decide)
  3. refutation on the witness ledger: every counterexample learned so
     far, appended and never removed
  4. exact decision over every 64-bit input and every callee (Z3,
     bit-vectors with uninterpreted functions); a counterexample it
     finds is appended to the ledger, so later rows refute at stage 3
Verdicts: equal (joined), differ (refuted), unknown (solver timeout).

Usage: python3 xdecide.py WSAT OBLIGATIONS.tsv [TIMEOUT_MS] > rows.jsonl
"""

import json
import resource
import subprocess
import sys
import time

sys.path.insert(0, __file__.rsplit("/", 1)[0] or ".")
from bv import decide, parse  # noqa: E402

M64 = (1 << 64) - 1


def wrap(v):
    v &= M64
    return v - (1 << 64) if v >> 63 else v


def mix(x):
    x = (x ^ (x >> 30)) * 0xBF58476D1CE4E5B9 & M64
    x = (x ^ (x >> 27)) * 0x94D049BB133111EB & M64
    return x ^ (x >> 31)


class Missing(Exception):
    pass


def ev(t, env, cnt):
    """eval's semantics; idx and call get one fixed interpretation, which
    is a valid interpretation of an uninterpreted function."""
    cnt[0] += 1
    if isinstance(t, str):
        if t.lstrip("-").isdigit():
            return wrap(int(t))
        if t not in env:
            raise Missing(t)
        return env[t]
    h, *k = t
    if h == "idx":
        return mix((hash(k[0]) & M64) ^ (ev(k[1], env, cnt) & M64)) & 0xFFFF
    if h == "call":
        acc = mix(hash(k[0]) & M64)
        for x in k[1:]:
            acc = mix(acc ^ (ev(x, env, cnt) & M64))
        return acc & 0xFFFF
    a = [ev(x, env, cnt) for x in k]
    if h == "+":
        return wrap(a[0] + a[1])
    if h == "*":
        return wrap(a[0] * a[1])
    if h == "-":
        return wrap(a[0] - a[1])
    if h == "neg":
        return wrap(-a[0])
    if h == "<<":
        return wrap(a[0] << (a[1] & 63))
    if h == ">>":
        return a[0] >> (a[1] & 63)
    if h in ("//", "%"):
        x, y = a
        if y == 0:
            return 0
        r = x % abs(y)
        return r if h == "%" else wrap((x - r) // y)
    if h == "&":
        return wrap(a[0] & a[1])
    if h == "|":
        return wrap(a[0] | a[1])
    if h == "^":
        return wrap(a[0] ^ a[1])
    raise ValueError(h)


def main():
    wsat, obl = sys.argv[1], sys.argv[2]
    tmo = int(sys.argv[3]) if len(sys.argv) > 3 else 10000
    rows = [l.rstrip("\n").split("\t") for l in open(obl) if l.strip()]
    t0 = time.perf_counter()
    with open(obl) as f:
        p = subprocess.run([wsat, "--engine", "decide"], stdin=f, capture_output=True, text=True, check=True)
    pre = {}
    vm = 0
    for l in p.stdout.splitlines():
        r = json.loads(l)
        if r.get("summary"):
            vm = r["vmhwm_kb"]
        else:
            pre[r["id"]] = r
    ledger = []  # learned counterexamples (variable assignments), append only
    out = []
    for rid, suite, a, b in rows:
        r = pre[rid]
        rec = {"id": rid, "suite": suite, "evals": r["evals"], "solver_s": 0.0, "ledger_evals": 0}
        if r["status"] == "refuted":
            rec.update(verdict="differ", stage="points")
            out.append(rec)
            continue
        if r["enodes"] and a == b:
            rec.update(verdict="equal", stage="identity")
            out.append(rec)
            continue
        ta, tb = parse(a), parse(b)
        hit = False
        cnt = [0]
        for env in ledger:
            try:
                if ev(ta, env, cnt) != ev(tb, env, cnt):
                    hit = True
                    break
            except Missing:
                continue
        rec["ledger_evals"] = cnt[0]
        if hit:
            rec.update(verdict="differ", stage="ledger")
            out.append(rec)
            continue
        ts = time.perf_counter()
        v, cx = decide(a, b, tmo)
        rec["solver_s"] = round(time.perf_counter() - ts, 4)
        rec.update(verdict=v, stage="solver")
        if v == "differ" and cx:
            # append only if the point reproduces the difference here
            try:
                c2 = [0]
                if ev(ta, cx, c2) != ev(tb, cx, c2):
                    ledger.append(cx)
                    rec["learned"] = True
            except Missing:
                pass
        out.append(rec)
    wall = time.perf_counter() - t0
    me = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    for rec in out:
        print(json.dumps(rec))
    print(json.dumps({"summary": True, "wall_s": round(wall, 4), "vmhwm_kb": max(vm, me), "ledger": len(ledger)}))


if __name__ == "__main__":
    main()
