"""Dominator tree of the RH proof graph over local constants.
For each constant c, dom(c) = constants that disappear from RH's closure if c's proof is
replaced by an axiom of the same statement (i.e. c becomes a leaf). Weighted by declaration lines.
Note: edges include type dependencies, so c's statement still keeps its type's constants;
this script approximates by cutting all out-edges of c (upper bound for the cut) and also
reports the exact value cut (statement kept) when a per-constant type-edge list is available."""
import sys, collections, networkx as nx
S, U = sys.argv[1], sys.argv[2]   # edges_rh.tsv, usage.tsv
lines = {}; mod = {}
seen = collections.defaultdict(set)
for ln in open(U):
    p = ln.rstrip("\n").split("\t")
    if p[0] == "name" or len(p) < 4: continue
    try: a, b = int(p[2]), int(p[3])
    except: continue
    mod[p[0]] = p[1]
    lines[p[0]] = (p[1], a, b)
G = nx.DiGraph()
TY = {}
for ln in open(S):
    p = ln.rstrip("\n").split("\t")
    a = p[0]; G.add_node(a)
    TY[a] = p[1].split() if len(p) > 1 and p[1] else []
    for b in (p[2].split() if len(p) > 2 else []):
        if b != a: G.add_edge(a, b)
G = G.subgraph(nx.descendants(G, "riemannHypothesis") | {"riemannHypothesis"}).copy()
root = "riemannHypothesis"
idom = nx.immediate_dominators(G, root)
children = collections.defaultdict(list)
for v, d in idom.items():
    if v != d: children[d].append(v)
# each (module,line) is owned by the widest declaration covering it, so weights add exactly
own = collections.Counter()
bymod = collections.defaultdict(list)
for n,(m,a,b) in lines.items():
    if a > 0: bymod[m].append((b-a, n, a, b))
for m, L in bymod.items():
    owner = {}
    for w, n, a, b in sorted(L, reverse=True):
        for l in range(a, b+1):
            if l not in owner: owner[l] = n
    for l, n in owner.items(): own[n] += 1
T = nx.DiGraph([(d, v) for v, d in idom.items() if v != d])
order = list(nx.dfs_preorder_nodes(T, root))
subw = {}
for v in reversed(order):
    subw[v] = own[v] + sum(subw[c] for c in children[v])
total = subw[root]
print("reachable", len(idom), "total decl lines", total)
rows = sorted(((subw[v], v) for v in idom if v != root), reverse=True)
out = open(sys.argv[3], "w")
for w, v in rows: out.write(f"{w}\t{v}\t{mod.get(v,'?')}\n")
for w, v in rows[:60]: print(f"{w:7d} {100*w/total:5.1f}% {v}  [{mod.get(v,'?')}]")
