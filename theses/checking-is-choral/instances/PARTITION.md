# The idol-semi partition

Cone partitions of the Lean development of clpi/idol-semi
(proofs/lean: the SemperProofs and Conform libraries) at its two
successive proof-tree heads, computed from the real import graph
by the method SPEC.md states. The machine-readable artifacts are
partition-h1.json and partition-h2.json beside this file; each
carries the module set, the internal edge set, the three cones,
the exact cross-cone edge list, per-cone line counts, and the
check files per cone. A verifier pass independent of the
partitioner checked both artifacts: cones disjoint, union equal
to the module set, cross-edge list exact against the edge set and
the assignment, line counts consistent. All checks pass at both
heads.

## Head two — 6c37120b16c7ce3871f20f738a30ed12df7f5064

156 modules, 267 project-internal import edges, dependency depth
25, 44,457 lines. External imports are only the standard library,
the Lean library, and Mathlib (eight import statements in total;
the development's own graph is the 267 edges).

- Cone 0: 48 modules, 15,640 lines, 7 check files.
- Cone 1: 68 modules, 13,173 lines, 13 check files.
- Cone 2: 40 modules, 15,644 lines, 3 check files.
- Cross-cone edges: 40, every one enumerated in the artifact.

## Head one — 00f9d46ffada471088f11c9f3d91130e8439ce0f

153 modules, 261 project-internal import edges, dependency depth
25, 43,411 lines. The step to head two changes twelve files in the
flatten and regroup area (1,234 insertions, 150 deletions) and
adds three modules.

- Cone 0: 55 modules, 15,274 lines, 10 check files.
- Cone 1: 35 modules, 15,316 lines, 1 check file.
- Cone 2: 63 modules, 12,821 lines, 12 check files.
- Cross-cone edges: 52, every one enumerated in the artifact.

## Structure notes

The development is one tightly woven whole: thirty entry points
(two library roots, five executable roots, twenty-three check
files) stand over a shared body — 118 of the 156 modules at head
two are reachable from more than one entry point. Entry-cone
splitting would hand every checker nearly the whole development;
the balanced topological partition above is what makes the split
a split. Line count is the load proxy the partitioner balances
on; it is a proxy, and the runs, when they happen, report real
wall-clock against it.
