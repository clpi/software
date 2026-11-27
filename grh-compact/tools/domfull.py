import sys, collections, networkx as nx
S, OUT = sys.argv[1], sys.argv[2]
G = nx.DiGraph(); mod = {}
for ln in open(S):
    p = ln.rstrip("\n").split("\t")
    mod[p[0]] = p[1]; G.add_node(p[0])
    for u in (p[2].split() if len(p) > 2 else []):
        if u != p[0]: G.add_edge(p[0], u)
loc = lambda n: mod.get(n, "?").split(".")[0] in ("Lib", "New", "Main", "Statements")
idom = nx.immediate_dominators(G, "riemannHypothesis")
ch = collections.defaultdict(list)
for v, d in idom.items():
    if v != d: ch[d].append(v)
T = nx.DiGraph([(d, v) for v, d in idom.items() if v != d])
order = list(nx.dfs_preorder_nodes(T, "riemannHypothesis"))
sz = {}; msz = {}
for v in reversed(order):
    sz[v] = 1 + sum(sz[c] for c in ch[v])
    msz[v] = (0 if loc(v) else 1) + sum(msz[c] for c in ch[v])
print("nodes", len(idom), "mathlib/core nodes", msz["riemannHypothesis"])
# Mathlib subtrees hanging directly under a local constant: a single local use carries them
rows = []
for v, d in idom.items():
    if v != d and not loc(v) and loc(d):
        rows.append((sz[v], v, mod.get(v), d, mod.get(d)))
rows.sort(reverse=True)
with open(OUT, "w") as f:
    for r in rows: f.write("\t".join(map(str, r)) + "\n")
# aggregate per local owner: mathlib constants carried only by that local constant's own proof
agg = collections.Counter(); ex = collections.defaultdict(list)
for s, v, m, d, dm in rows: agg[d] += s; ex[d].append((s, v))
print("local constants that alone carry mathlib theory (top 40):")
for d, s in agg.most_common(40):
    top = ", ".join(f"{v}({k})" for k, v in sorted(ex[d], reverse=True)[:3])
    print(f"{s:6d}  {d}  [{mod.get(d)}]  via {top}")
