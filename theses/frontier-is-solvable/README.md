# software-frontier-is-solvable

A standalone Lean 4.19 companion for exact finite qualification frontiers, derived from one authoritative behavioral hypergraph. This library introduces no second graph or evidence store. A caller supplies candidate identities, graph-derived eligibility, and selected cost axes.

## Machine-checked results

`Frontier.lean` contains 14 named theorems:

- Strict Pareto dominance is irreflexive and transitive; equal objective vectors do not strictly dominate each other.
- **Insertion:** the new frontier consists exactly of old frontier members not dominated by the inserted identity, plus that identity when no old eligible identity dominates it.
- **Retraction:** an eligible survivor becomes nondominated exactly when every former eligible dominator has been removed. Multiple independent dominators are retained correctly.
- Old nondominated survivors remain nondominated under removal; any live dominator blocks resurrection.
- Extensionally equal qualification and comparison views produce the same frontier, independently of graph storage/index layout.
- A no-worse-than-baseline guard enforces every selected objective, not merely absence of domination by the baseline. Its frontier is also nondominated among all eligible candidates.
- The baseline-guarded frontier is nonempty whenever the baseline remains among eligible candidates.
- The executable list evaluator matches the eligibility/nondominance specification exactly.
- The executable finite-axis comparison matches componentwise no-worse plus strict improvement on at least one selected axis.
- Every nonempty finite candidate list has a nondominated member under any strict partial order.

`Tests.lean` contains 15 kernel-reduced examples, including an incomparable tradeoff, equal-valued identities, duplicate identity occurrences, empty axes, rejected candidates, dominated insertions, improving insertions, retraction/resurrection and multiple dominators. Two explicit counterexamples show:

1. Pareto membership alone does not guarantee no regression against a baseline.
2. Storing only the current frontier discards information required for exact later retraction: two candidate populations with the same current frontier can have different frontiers after removing its winner.

## Reproduce

Install the pinned toolchain from `lean-toolchain`, then:

```sh
./check.sh
```

Or supply `LEAN=/absolute/path/to/lean ./check.sh`. The script fails on compilation errors, warnings, or prohibited proof escapes; every named theorem has its axiom dependencies printed. No custom axioms or admitted proofs are used. Some results use Lean's standard `propext`, `Classical.choice`, and `Quot.sound`; others are axiom-free. The included `CHECK.log` records the actual successful compiler run.

## Engineering interpretation

Qualify candidates from the authoritative graph at a named snapshot. Evaluate the frontier over those candidates and the selected metric view. Use the insertion/retraction equations to maintain that view, retaining dominated candidates or equivalent reconstructible source data. The equations justify incremental membership updates; the provided executable evaluator is deliberately a full-scan reference oracle, not a claimed optimized incremental runtime.

An observation appends evidence; it need not improve candidate cost or preserve eligibility. Qualification retraction can resurrect previously dominated candidates. Ties retain separate identities. List duplicates do not change membership but remain duplicate output entries; normalize identities upstream when set cardinality is required. Deterministic input order yields deterministic output order; canonical serialization/sorting is not supplied here.

A raw incidence matrix is not a proof of semantic equivalence. The graph-to-qualification adapter and authorized transfer certificates remain responsible for valid eligibility. The companion proves frontier calculations from these supplied views, not physical runtime measurements, semantic lowering, or completeness of the candidate generator. Axis costs are integer-valued and minimization-oriented; a caller must use consistent units, scope, and orientation. Empty axes intentionally make every eligible candidate a tie.

The finite exact reference calculation examines all eligible candidate pairs and selected axes; its straightforward comparison work is O(m²a) for m candidates and a axes. No empirical performance claim, universal speedup, global optimum beyond the supplied candidate population, or automatic strict growth per witness follows from these theorems.
