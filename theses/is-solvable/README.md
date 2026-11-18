# software-is-solvable

A Lean 4.19 reference formalization of **witness-compounding search and resolution**, independent of a programming language or application domain.

The authoritative object is a scoped behavioral hypergraph. Its admitted witness atoms are roots; its finite-premise transfer/composition certificates are hyperedges. Saturation, qualification colors, incidence/interaction matrices, and finite candidate catalogues are derived views. A Merkle commitment can identify this object; hashing is not itself a proof of semantic equivalence.

## Checked result

For graphs `G` and newly admitted batch `W`, write `K(G)` for the least finite-derivation closure. The implementation proves:

1. **Append preservation:** `K(G) ⊆ K(G ∪ W)`, including when W introduces new rules, not just roots.
2. **Cross-premise compounding:** `K(G ∪ W) = K(saturate(G) ∪ saturate(W))`. The right side is **reclosed**. Merely unioning old closures loses mixed-premise consequences.
3. **Resolution-bound expansion vector:** name finite probe lists `Pᵢ` over the authority's exact scoped atoms. `ρᵢ(G) = count {p in Pᵢ : p ∈ K(G)}`. Every coordinate is nondecreasing under append, when classifiers are exact. Executable closure is proved exact and connected to this theorem.
4. **Exact marginal gain:** `ρᵢ + (ρᵢ′ − ρᵢ) = ρᵢ′`. A coordinate strictly increases exactly when at least one of its probes becomes newly supported. Duplicate and already-derived witnesses can have zero delta.
5. **Commutative, associative, idempotent knowledge merge:** raw batch lists may repeat atoms; root/rule membership and resulting closure do not count repeats as new semantic support.
6. **Executable selection:** a named total Boolean qualification gate is evaluated over every entry in the reference configuration catalogue. The resulting list contains exactly the catalogue entries satisfying the gate.
7. **Withdrawal projection:** filtering live roots/rules cannot create a new derivation absent from historical authority. Unsupported cycles cannot sustain themselves after their only origin is withdrawn. Other independent support paths survive.

A probe means a precisely specified **support obligation**, not an inferred truth or a probability. Use distinct probes for cardinality axes. Repeated probes instead define explicit multiplicity weights. Coordinate labels and probes must remain fixed for a before/after comparison. New axis domains require an explicit embedding/comparison policy; a renamed coordinate is not automatically comparable.

## Resolution, candidates, and qualification are different

The resolution vector counts supported obligations. It is a lower bound on resolved support in the named probe scopes. It does **not** measure remaining runtime, probabilistic confidence, or a guaranteed count of feasible software designs. Negative outcomes are first-class atoms and can improve resolution while changing a favorable qualification to conflict or exclusion.

The example catalogue enumerates subsets of closure atoms. `catalogue_compounding` proves its exact append multiplier: `entries_after = entries_before × 2^Δk`, where Δk is the new closure-list length minus the old length. A duplicate append has Δk=0 and multiplier 1. Its **enumerated entry count** is exactly `2^k` for a closure list of length k. With a unique universe it represents distinct subsets. This is not a claim that every subset is executable, composable, qualified, or optimal. The executable gate handles those constraints; its exact accepted result may shrink or be empty. No theorem assumes exponential growth on every append.

Positive and negative support are independent. The four color codes are unknown=0, positive-only=1, negative-only=2, conflict=3. These are information statuses, not a numeric quality ordering. History is append-only; live eligibility is deliberately not monotone.

## Authority and trust boundary

- `Graph` and `Batch` use a generic atom type. Production atoms must bind content, lineage, scope, venue/environment, harness, premises, and polarity as required by the contract. Admission/authentication and correct encoding are prerequisites, not silently proved here.
- All hyperedge premises are conjunctive. Cycles use least finite derivations, not self-supporting greatest fixed points.
- `Qualification.soundness` proves semantic truth only from valid roots and truth-preserving admitted rules. Merely recording a claim does not make it true.
- Reference enumeration is executable, terminating, and exponentially expensive. It supplies an oracle/specification for optimized worklists; this repository does not claim a production performance win.
- Withdrawals are supplied as an already-resolved dead-root/dead-edge projection. Authorization, event identity conflicts, and timestamp policy belong to admission, not this proof's generic filter.
- A native egraph, ledger/MMR, database, compiler, telemetry adapter, external solver, or deployed release is not verified merely because it can emit this model.

## Files and proof evidence

- `Qualification.lean`: existing closure/soundness core reused from `clpi/software-optimality`.
- `ExecutableClosure.lean`: existing exhaustive closure evaluator and `close_exact` bridge, reused from that project.
- `Hyperlattice.lean`: authority joins, semantic compounding, numeric resolution vector and strict/zero gain laws.
- `WitnessExecutable.lean`: executable batches/classifiers, append-to-vector bridge, catalogue/qualification and matrix views, live filtering.
- `WitnessTests.lean`: kernel-checked concrete controls for synergy, duplicates, redundancy, rule-only novelty, negative evidence, cycles, withdrawals, surviving alternate origins, malformed domains, and empty qualification.

Run `LEAN=/path/to/lean ./check.sh`. No Mathlib or external Lean dependency is required. `lean-toolchain` pins 4.19.0. Checks fail on warnings and proof escapes. `#print axioms` exposes ordinary Lean foundational dependencies (`propext`, `Quot.sound`, and classical choice in the reference completeness proof); there are no custom axioms or admitted theorems.

## Engineering consequences

Each append can be recorded with its before/after root, exact resolution vector delta, newly supported probes, newly rejected/conflicting qualification cases, and derivation dependencies. This is incremental *accounting*: it does not require pretending a regression is improvement. Saturated cached views may be reused, but cross-view rules must be reapplied. The exact reference result is an independently testable target for optimized implementations.
