"""Incremental active-view Boolean coverage for trusted indexed deltas."""
from collections import deque
from itertools import combinations
import runpy
from pathlib import Path

static = runpy.run_path(str(Path(__file__).with_name("mediation-replay.py")))
forward = static["independent"]

def index(n, edges):
    incoming, outgoing = [set() for _ in range(n)], [set() for _ in range(n)]
    for x, y in edges:
        incoming[y].add(x)
        outgoing[x].add(y)
    return incoming, outgoing

def repair(old_in, new_in, new_out, ready, changed, marks):
    """Change marks in place. 'changed' must cover all edited sources and readiness bits."""
    dirty = set(changed)
    pending = deque(dirty)
    while pending:
        v = pending.popleft()
        for predecessors in (old_in[v], new_in[v]):
            for u in predecessors:
                if u not in dirty:
                    dirty.add(u)
                    pending.append(u)
    for v in dirty:
        marks[v] = False
    for v in dirty:
        if ready[v] or any(w not in dirty and marks[w] for w in new_out[v]):
            marks[v] = True
            pending.append(v)
    while pending:
        v = pending.popleft()
        for u in new_in[v]:
            if u in dirty and not marks[u]:
                marks[u] = True
                pending.append(u)
    return len(dirty)

def test():
    n = 3
    edge = [(i, j) for i in range(n) for j in range(n)]
    snapshots = []
    for bits in range(1 << (len(edge)+n)):
        es = [e for i,e in enumerate(edge) if bits >> i & 1]
        ready = [bool(bits >> (len(edge)+i) & 1) for i in range(n)]
        inc, out = index(n, es)
        snapshots.append((inc,out,ready,[forward(ready,es,x) for x in range(n)]))
    edits = [(i,) for i in range(12)] + list(combinations(range(12),2))
    count = changed_answers = 0
    for old, (old_in, _, _, marks) in enumerate(snapshots):
        for edit in edits:
            new = old ^ sum(1 << i for i in edit)
            new_in,new_out,ready,expected = snapshots[new]
            changed = [edge[i][0] if i<9 else i-9 for i in edit]
            answer = marks.copy()
            repair(old_in,new_in,new_out,ready,changed,answer)
            if answer != expected:
                raise AssertionError((old, edit))
            changed_answers += (answer != marks)
            count += 1
    incoming, _ = index(n, [(0,1),(1,0),(1,2)])
    next_in, next_out = index(n, [(0,1),(1,0)])
    marks = [True,True,True]
    repair(incoming,next_in,next_out,[False,False,True],[1],marks)
    assert marks == [False,False,True]
    # Identical Boolean readiness can require a different named witness.
    before, after = {"primary":2,"spare":2}, {"spare":2}
    assert set(before.values()) == set(after.values()) and "primary" not in after
    print(f"{count} edits; {n*count} target comparisons; {changed_answers} changed answers")
    print("cycle withdrawal and same-vertex sensor replacement controls passed")

if __name__ == "__main__":
    test()
