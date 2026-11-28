"""Run wsat configurations on an obligation file and record per-row
results plus process time and peak memory.

Usage: python3 bench.py WSAT OBLIGATIONS.tsv OUT.json NAME=FLAGS [NAME=FLAGS ...]
FLAGS is a space-separated flag list, e.g. 'witness=--engine witness'.
"""

import json
import resource
import subprocess
import sys
import time


def run(wsat, obl, flags):
    before = resource.getrusage(resource.RUSAGE_CHILDREN)
    t0 = time.perf_counter()
    with open(obl) as f:
        p = subprocess.run([wsat] + flags.split(), stdin=f, capture_output=True, text=True, check=True)
    wall = time.perf_counter() - t0
    after = resource.getrusage(resource.RUSAGE_CHILDREN)
    rows = [json.loads(l) for l in p.stdout.splitlines() if l.strip()]
    summ = [r for r in rows if r.get("summary")]
    rows = [r for r in rows if not r.get("summary")]
    return {
        "vmhwm_kb": summ[0]["vmhwm_kb"] if summ else None,
        "flags": flags,
        "wall_s": round(wall, 4),
        "cpu_s": round((after.ru_utime - before.ru_utime) + (after.ru_stime - before.ru_stime), 4),
        "rows": rows,
    }


def main():
    wsat, obl, out = sys.argv[1:4]
    res = {}
    for spec in sys.argv[4:]:
        name, flags = spec.split("=", 1)
        res[name] = run(wsat, obl, flags)
    json.dump(res, open(out, "w"), indent=0)


if __name__ == "__main__":
    main()
