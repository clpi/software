# Recomputing replica placements after a hub outage

| Before | After |
|---|---|
| 4 nondominated placements with hub online | 3 nondominated placements with hub offline |

Three client sites lie at 0, 2, and 6. Minimize replica count and the largest distance from any client to a serving replica. The hub outage removes its hosting eligibility; the clients at that location still need service.

## Why the bound holds

The checker derives the distances from the site coordinates, enumerates all eight masks, excludes the empty placement, and proves frontier membership against every layout. With the hub offline, either endpoint alone has cost (1, 6), and both endpoints together have cost (2, 2). Filtering only the former winners incorrectly returns just the two-endpoint plan.

## Replay

Run from the repository root with Lean 4.19.0 available.

```sh
sh examples/check.sh
```

The runner checks the [proof](ReplicaPlacement.lean) with warnings as errors and prints the computed result and theorem dependencies.

The [verification transcript](verification.txt) includes the observed outputs and the rejected counterexample mutation.

## Scope

Distances are line units and every replica has the same unit cost. Equal-cost layouts retain separate identities. Actual network latency, capacity, and availability need different inputs.
