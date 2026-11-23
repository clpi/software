# Spec — the choral split of one cold gate

The registered experiment this repo serves, stated at the
resolution an executing lane needs. The theorem side is proved in
proof/; this spec governs the runs.

## Subject

One proof repo whose cold gate is the estate's largest: the Lean
development under proofs/lean in clpi/idol-semi — two libraries
(SemperProofs, Conform), five executables, twenty-three check
files. Its gate, as its own continuous integration defines it:
fetch the prebuilt dependency artifacts for the pinned dependency
commit (the dependency is never compiled), build the whole
development, scan the sources and the build log for admitted
proofs, and elaborate every check file, requiring each one's axiom
report to name only the three standard principles. The verdict is
the gate's exit state; the audit is the per-file axiom report set.

The gate runs under the toolchain the development pins in its own
toolchain file (a newer release than the estate's usual pin; the
pin is the development's, and every checker runs exactly it).

## Heads

Two successive heads of the proof tree, read from the repo itself:
the newest commit touching the proof tree and its predecessor
touching the proof tree. At the founding of this repo those are
6c37120b16c7ce3871f20f738a30ed12df7f5064 and
00f9d46ffada471088f11c9f3d91130e8439ce0f; the estate's standing pin
carries the first head's proof tree unchanged.

## Partition

From the real import graph of the proof tree at each head — never
from file names: parse every module's imports, keep the
project-internal edges, and assign each module to exactly one of
three cones by a balance-capped greedy pass in topological order
(each module prefers the cone holding most of its dependencies,
under a load cap by line count), with deterministic restarts
keeping the best-scoring assignment. The partition artifact lists
every cone's modules, every cross-cone edge, and the check files
per cone, and a separate verifier pass checks the artifact:
cones disjoint, union equal to the module set, the cross-edge
list exactly the set of edges the assignment makes cross, line
counts consistent. The registered premise — the partition covers
every cross-file dependency — is this verified enumeration: a
cross-cone dependency is covered when the receiving cone is
supplied the producing cone's checked artifact for it.

## Split procedure

Per head, per cone, on a separate checker host, in a clean tree:

1. Fetch the same prebuilt dependency artifacts as the whole gate.
2. Build the cone's modules in topological order. For each
   cross-cone dependency, take the artifact from the cone that
   owns the dependency module, produced in that cone's own run at
   the same head. A cone whose dependencies include another cone's
   modules starts those modules' builds only from the received
   artifacts, never by rebuilding them.
3. Run the source scan over the cone's own sources, and elaborate
   the cone's check files, collecting their axiom reports.

Join: the split verdict is accept exactly when every cone's build
and scan accept; the split audit is the union of the cones' axiom
reports, compared as a set per check file against the whole
gate's.

## Decision rule, registered in advance

The split gate is adopted if its verdict and its axiom audit
match the whole gate's exactly, on both successive heads. A
verdict mismatch on either head falsifies the split. An axiom
audit mismatch on either head falsifies the split. The wall-clock
of the split (the slowest cone, plus exchange time) is reported
against the whole gate's wall-clock at the same head on the same
class of host; no fraction is claimed before it is measured.

## Outcome classes

Five, registered with the item: adopted; falsified by a verdict
mismatch; falsified by an audit mismatch; blocked before any run
(the subject or its gate cannot be obtained or built as
specified); blocked at the hosts (fewer than three checker hosts
with the pinned toolchain and the room to build).

## Development route

When adopted, the fleet's gate lanes run split gates for this
development, and the parked re-gates behind gate cost get a priced
route back. Until adopted, the whole gate remains the only gate.
