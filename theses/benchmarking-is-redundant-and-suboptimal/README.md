# software-benchmarking-is-redundant-and-suboptimal

A machine-checked **conditional redundancy and dominance theorem**, not a
blanket claim that physical measurement is unnecessary. Lean 4.19.0, no mathlib.

## Exact result

For a named evidence snapshot B and admitted finite-premise hypergraph rules R:

1. A result is logically redundant exactly when every atom it contributes is
   already derivable. Adding that result leaves the entire derivation closure
   unchanged (`TestingRedundancy.redundancy_iff`). This is stronger than leaving
   one dashboard cell unchanged and preserves future compounding with new
   evidence while the relevant certificates remain valid.
2. A plan p can replace plan q for every encoded purpose when p's evidence
   derives all of q's evidence (`coverage_preserves_purpose`).
3. If replacement costs no more on every declared axis and strictly less on
   at least one, q is not Pareto optimal among admitted plans
   (`dominated_not_pareto`). This is a genuine dominance statement, not merely
   that the replacement happens to be on a frontier.
4. In particular, a fully covered, positive-cost plan is dominated by omission
   (`covered_positive_plan_dominated`), **if omission is admissible**. Checking
   stored certificates, retrieving evidence and operational effects must be
   charged or represented. Zero-cost `skip` describes pure omission; it must
   not silently stand for an expensive reconstruction procedure.
5. Prospective removal of an experiment needs coverage of **every possible
   outcome** (`all_outcomes_redundant`). One already-known passing result does
   not make a flaky experiment redundant. An outcome catalogue must cover the
   real experiment; this project does not derive such completeness by fiat.

The general type `Atom` must encode the distinctions the purpose cares about:
artifact, lineage, workload, venue, environment epoch, protocol, units,
aggregation, polarity, sample identity, effects and dependencies as applicable.
`Receipt` is a deliberately small executable illustration, not a full schema.
A new receipt identity is not proof of statistical independence.

## Tests and boundaries

`Tests.lean` contains kernel-checked examples/counterexamples for replay,
fresh samples, epoch/venue/protocol changes, jointly required samples,
positive-cost redundancy, zero-cost non-strictness, coverage/cost tradeoffs,
functional equality without cost equality, flaky outcomes, max aggregation,
withdrawals, and purpose-only redundancy with novel unrelated evidence.

A cost is a declared natural-number vector, not an inferred physical runtime.
Equal functional outputs do **not** imply equal runtime. The cost relation may
be established by an exact accounting model or a separately scoped empirical
comparison. Empirical claims must retain their uncertainty and sampling scope.
No speedup or statistical confidence is claimed by these symbolic proofs.

Strict local savings compose under additive surrounding costs (proved).
Parallel makespan can absorb a local saving (counterexample: max 1 10 = max 2
10); arbitrary venue-parallel speedups require a different certified cost law.

Semantic truth requires valid roots and truth-preserving rules
(`derived_result_sound`). Content addressing establishes identity, not the
truth/completeness of dependency metadata, policies or certificates. Withdrawn
origins remove live derivations; history remains immutable.

## Files and provenance

- `Qualification.lean`: conjunctive hypergraph closure foundation, copied
  unchanged from the companion software-testing-is-redundant workspace.
- `Redundancy.lean`: its exact closure redundancy and countermodel theorems,
  likewise copied unchanged. This is shared proof code, not a separate graph.
- `Benchmark.lean`: new plan dominance, purpose preservation, prospective
  redundancy, cost composition and receipt-scope theorems.
- `Tests.lean`: finite regressions/counterexamples.

## Reproduce

```
lean --version  # Lean 4.19.0
./check.sh
```

`check.sh` fails immediately on the first compiler error and treats warnings as
errors. It scans all proof sources for `sorry`, `admit`, custom `axiom` and
`native_decide`, rejects `sorryAx` in printed reports, and runs deliberate
admission/type-error rejection controls plus four forbidden-token scanner
controls. This is a source guard, not a general Lean metaprogram security
sandbox. `#print axioms` lists foundational assumptions. New printed benchmark
theorems use no axioms. An inherited extensional-view theorem uses Lean's
standard `propext` and `Quot.sound`; no theorem uses `sorryAx` or an admission.
This is a proof project, not yet a benchmark runner, empirical venue study,
complete experiment optimizer, or proof that all hand-authored benchmarks can
be deleted. Independent review is required before publication.
