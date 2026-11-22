"""Finite, unweighted reachability control. No deployment validation."""
from collections import deque

def ready_mask(n, sensors):
    ready = [False] * n
    for v, deployed, healthy, faithful in sensors:
        ready[v] |= deployed and healthy and faithful
    return ready

def observe(ready, edges):
    reverse = [[] for _ in ready]
    for x, y in edges:
        reverse[y].append(x)
    marked = ready.copy()
    work = deque(v for v, active in enumerate(ready) if active)
    scans = pops = 0
    while work:
        y = work.popleft()
        pops += 1
        for x in reverse[y]:
            scans += 1
            if not marked[x]:
                marked[x] = True
                work.append(x)
    return marked, pops, scans

def independent(ready, edges, x):
    seen, prev = {x}, set()
    while seen != prev:
        prev = seen
        seen = seen | {y for u, y in edges if u in seen}
    return any(ready[u] for u in seen)

def controls():
    n = 3
    possible = [(u,v) for u in range(n) for v in range(n)]
    count = 0
    for graph in range(1 << len(possible)):
        edges = [p for i,p in enumerate(possible) if graph >> i & 1]
        for mask in range(1 << n):
            ready = [bool(mask >> i & 1) for i in range(n)]
            result, pops, scans = observe(ready, edges)
            if result != [independent(ready, edges, x) for x in range(n)]:
                raise AssertionError((graph,mask))
            if pops != sum(result) or scans > len(edges):
                raise AssertionError("duplicate processing")
            count += 1
    edges = [(2,1), (1,0)]
    for mask in range(8):
        active = ready_mask(n, [(0, *(bool(mask >> i & 1) for i in range(3)))])
        if observe(active, edges)[0][2] != (mask == 7):
            raise AssertionError(mask)
    print(f"{count} graph/sensor configurations; {count*n} target comparisons; 8 sensor-flag controls")

if __name__ == "__main__":
    controls()
