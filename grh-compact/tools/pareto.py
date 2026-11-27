"""Exact single-cut Pareto front. Cutting X = keep X's statement (type edges), drop its proof
(value edges). remaining(X) = owned decl lines reachable from RH after the cut.
stmt(X) = owned decl lines reachable from X's type alone (what the assumption mentions)."""
import sys, collections, json, networkx as nx
S, U, D, OUT = sys.argv[1:5]
lines = {}
for ln in open(U):
    p = ln.rstrip("\n").split("\t")
    if p[0] == "name" or len(p) < 4: continue
    try: lines[p[0]] = (p[1], int(p[2]), int(p[3]))
    except: pass
own = collections.Counter(); bymod = collections.defaultdict(list)
for n, (m, a, b) in lines.items():
    if a > 0: bymod[m].append((b - a, n, a, b))
for m, L in bymod.items():
    owner = {}
    for w, n, a, b in sorted(L, reverse=True):
        for l in range(a, b + 1): owner.setdefault(l, n)
    for l, n in owner.items(): own[n] += 1
VAL = {}; TY = {}
for ln in open(S):
    p = ln.rstrip("\n").split("\t")
    TY[p[0]] = [x for x in (p[1].split() if len(p) > 1 else []) if x != p[0]]
    VAL[p[0]] = [x for x in (p[2].split() if len(p) > 2 else []) if x != p[0]]
def reach(roots, cut=frozenset()):
    seen = set(); st = list(roots)
    while st:
        v = st.pop()
        if v in seen: continue
        seen.add(v)
        st.extend(TY.get(v, []) if v in cut else VAL.get(v, []))
    return seen
W = lambda s: sum(own[v] for v in s)
base = reach(["riemannHypothesis"]); total = W(base)
cands = [l.split("\t")[1] for l in open(D) if int(l.split("\t")[0]) >= 0.004 * total]
res = []
for x in cands:
    r = reach(["riemannHypothesis"], frozenset([x]))
    st = reach(TY.get(x, []))
    res.append({"name": x, "module": lines.get(x, ("?",))[0], "remaining": W(r), "removed": total - W(r),
                "stmt_lines": W(st), "stmt_consts": len(st)})
# Pareto: minimize remaining and stmt_lines
res.sort(key=lambda d: (d["remaining"], d["stmt_lines"]))
front = []; best = float("inf")
for d in res:
    if d["stmt_lines"] < best: front.append(d); best = d["stmt_lines"]
json.dump({"total": total, "all": res, "front": front}, open(OUT, "w"), indent=1)
print("total", total, "candidates", len(res))
for d in front: print(f'{d["removed"]:7d} {100*d["removed"]/total:5.1f}% removed | stmt {d["stmt_lines"]:6d} lines {d["stmt_consts"]:5d} consts | {d["name"]}')
