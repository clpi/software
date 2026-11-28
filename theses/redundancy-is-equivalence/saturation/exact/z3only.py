"""State-of-the-art floor: Z3 alone on every row, no pre-filter, same
finest-grain semantics (bv.py). Usage: python3 z3only.py ROWS.tsv [TIMEOUT_MS]"""
import json, resource, sys, time
sys.path.insert(0, __file__.rsplit("/", 1)[0] or ".")
from bv import decide  # noqa: E402

tmo = int(sys.argv[2]) if len(sys.argv) > 2 else 10000
t0 = time.perf_counter()
for l in open(sys.argv[1]):
    if not l.strip():
        continue
    rid, suite, a, b = l.rstrip("\n").split("\t")
    ts = time.perf_counter()
    v, _ = decide(a, b, tmo)
    print(json.dumps({"id": rid, "suite": suite, "verdict": v, "solver_s": round(time.perf_counter() - ts, 4)}))
print(json.dumps({"summary": True, "wall_s": round(time.perf_counter() - t0, 4),
                  "vmhwm_kb": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}))
