# software-fuzzing-is-suboptimal

Machine-checked **conditional** suboptimality of evidence-generation plans, not a universal claim that fuzzing is inferior. Lean 4.19.0, Std only. No project axioms, admissions or native-decision escape.

## What is proved

A plan summary contains covered goals and declared cost, under one fixed semantics / venue / workload / units contract. `Dominates a b` means every goal covered by b is covered by a, and a costs no more. Strict dominance requires strictly lower cost or an additional goal.

* Dominance is transitive and preserves budget feasibility and required-goal coverage.
* Replacing a subplan with a dominating one preserves dominance in an explicitly additive-cost, union-coverage composition. Positive cost savings stay strict. Coverage-only advantages can disappear in a larger context.
* A certified replay whose entire goal coverage is already retained is strictly dominated by omission when its cost is positive.
* Pointwise dominance on deterministic seed executions lifts to their whole finite seed campaign, including repeated seeds and their repeated costs.
* The executable `certify` checks matching contracts, every finite goal, and strictly reduced declared cost. `certify_exact` characterizes exactly its acceptance; `certified_strict` connects accepted certificates to the mathematical relation. Equal costs are deliberately not accepted by this cost-strict checker even if coverage improves.

These are model theorems, not fabricated benchmark results or proofs that a particular deployed engine is faster.

## Adversarial fixtures

The three-world oracle makes adaptivity substantive. A probe reveals the world; a targeted hit discovers the goal; each action costs one. A two-query feedback policy succeeds in every world. **Every fixed two-query plan misses a world** (including plans using the probe). Conversely, with the target already justified, a one-query targeted hit strictly dominates that adaptive policy. The oracle and probe cost are explicit model assumptions, not an assertion about arbitrary software.

A fresh independent sample is modeled as a distinct qualification goal: deleting it is *not* a dominating replacement. Thus counting/flakiness requirements cannot silently reuse the duplicate-seed theorem. Other tests reject missing coverage, higher/equal cost, mismatched contract IDs, and show repeated seeds still incur cost.

## Evidence boundary and stochastic interpretation

Seeds are explicit deterministic inputs. A seed list is an execution catalogue, **not a probability distribution**. No hit probability, confidence interval, independence, generalization or expected-runtime conclusion is proved. Such a claim needs a separately specified distribution, oracle and cost model. Actual execution time and measurement validity are not consequences of the natural-number cost arithmetic.

Contract IDs and plan fields are not trusted merely because a submitter supplies them. Integration must bind authoritative contract commitments, measured costs and certified coverage to the actual run. The checker proves comparison of submitted summaries, not that summaries faithfully describe execution. Goals may encode traces, input/output relations, intent obligations or sample identities; the theorem does not manufacture these semantics from set membership.

The findings can be recorded as derived qualification views over an authoritative hypergraph. This standalone library does not create a second authoritative graph or implement Merkle authentication, lineage transfers, withdrawals, scheduler implementation, or runtime instrumentation.

## Reproduce

Install the pinned toolchain, then run `./check.sh` (or `LEAN=/path/to/lean ./check.sh`). Run `./negative-controls.sh` with the same LEAN variable to verify rejection of a proof hole and an invalid proof. `CHECK.log` records the audited local run; `SHA256SUMS` binds source and documentation. `#print axioms` exposes dependencies: core algebraic theorems need none; finite decision/simplification uses Lean's standard `propext`/`Quot.sound`, never a project axiom.

No claim of universal Pareto optimality is made. The exact gain is a checked strict comparison under the named qualification contract, with a countermodel demonstrating why unconditional fuzzing inferiority is false.
