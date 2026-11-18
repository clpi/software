# software-testing-is-redundant

**Machine-checked exact redundancy criterion for qualification obligations.**
A hand-written test is redundant precisely when its complete scoped obligation
is already supported by the qualification closure. Its human authorship is not
relevant. A blanket claim that every hand-written test is redundant is false;
this package proves a finite counterexample, as well as the strongest exact
replacement theorem.

## Main result

Let `B` be live admitted support atoms and `R` the certified hyperedges of the
single behavior hypergraph. An atom must include every distinction relevant to
the claimed qualification: artifact/lineage, environment, input, effect, oracle,
trust, polarity, experiment identity and observation scope as appropriate.
`Cl(B)` is finite-derivation closure under conjunctive hyperedges `R`.
For a suite `T`:

```
T ⊆ Cl(B)  iff  Cl(B ∪ T) = Cl(B)
```

This is `redundancy_iff`. It is both necessary and sufficient; not merely the
sufficient assertion that duplicate tests can be skipped. It is independent of
Idol, a programming language, the test author, and the way evidence was produced.

### Structural consequences actually checked

* **Future composition:** covered obligations remain redundant under any further
  appended evidence and added inference rules, while existing supports and
  certificates remain valid (`contextual_redundancy`).
* **Substitutable evidence bases:** bases with the same closure are interchangeable
  under arbitrary future evidence joins (`compounding_congruence`).
* **Every derived view:** same closure preserves any deterministic function of it,
  including lawful/unlawful/conflict/unknown colors, incidence/interaction views,
  and gates that depend only on those atoms (`every_derived_view_preserved`).
  This does not cover gates depending on omitted counts, timing, metadata or cost.
* **Exact logical necessity:** an obligation is derivable iff it holds in every
  closed-set model of the roots/rules (`derivable_iff_all_models`). A missing
  obligation has an explicit countermodel, namely the least closure itself.
  These are models of this admitted Horn hypergraph, not a completeness theorem
  for all physical executions or an arbitrary language semantics.
* **Duplicate versus novel:** a repeated derived atom adds nothing; an actually
  new atom strictly expands closure (`singleton_duplicate`,
  `novel_witness_strict`). Growth need not be strict for every append.
* **Acceptance:** adding a test predicate leaves the compatible-model acceptance
  set unchanged iff existing evidence entails that predicate
  (`acceptance_unchanged_iff`).
* **Independent oracle:** models with identical observations but different test
  verdicts defeat every deterministic predictor using only those observations
  (`observational_independence`). A two-state example suffices.

## What can be eliminated

Once all encoded test obligations are covered, their *additional logical
requirements* and duplicate qualification records can be eliminated without
changing closure or its derived gate answers. Automatically generated suites
can replace manual suites if their closures coincide. No separate witness graph
is introduced: relations and views are over one qualification hypergraph.

This is not permission to label every test passed. A predicate being entailed is
not the same event as running an executable in a target environment. If a gate
requires an actual fresh run, latency sample, instrumentation result or minimum
independent sample count, that receipt is part of the obligation. It cannot be
replaced by the truth of a different proposition. Conversely, no hand-written
wrapper is needed merely to restate a fully derived obligation.

## Boundary tests that prevent vacuous overclaims

`Tests.lean` checks:

1. A two-model exact executable redundancy decision, positive and negative cases.
2. A new manual requirement not entailed by any existing evidence, with no appeal
   to undecidability or infinite behavior.
3. Equal return values with different effects: return-only equivalence is not
   whole-behavior qualification.
4. A conjunctive two-premise edge: one premise alone is insufficient.
5. Duplicate receipt versus new observation identity; opposite support polarity.
6. Two equal outcomes count as two trials, not one, for a count threshold.
7. Withdrawal invalidates prior derivability. Re-evaluate at the named snapshot;
   the contextual theorem is intentionally not a theorem about deletions.

Independence, noninterference and exact semantic/effect coverage are obligations
of a supplied inference certificate, not conclusions inferred from equal hashes.
Stochastic receipt counts do not prove independence or a population error rate.
Performance/no-regression claims need separately comparable measured costs.
Testing sufficiency does not itself prove that deleting tests makes every metric
better, nor that their harness or compiler is correct.

## Executable scope

`redundantOn models evidence test` is a Boolean list evaluator with a proved iff
specification. Its global conclusion requires a proof that the supplied model
list covers the intended model domain. This executable is linear in catalogue
size plus evaluation costs; it does not enumerate or solve an arbitrary source
program. Hypergraph closure theorems are proposition-level Lean proofs, not a
claim of an implemented incremental production closure engine.

## Build

Pinned version: Lean 4.19.0, no external libraries.

```
lake build
# or LEAN_BIN=/path/to/lean ./check.sh
```

`check.sh` compiles every module with warnings treated as errors, runs negative
compiler/admission controls, prints theorem axiom reports, and fails immediately
on any unexpected result. No custom axioms, `sorry`, `admit` or `native_decide`.
Lean's standard `propext` and `Quot.sound` appear in extensionality proofs.

`Qualification.lean` is copied unchanged from the existing qualification proof
family supplied in `/workspace/shared/qualification-proof` during development.
It supplies the least conjunctive hypergraph closure, soundness and withdrawal
lemmas. The two new modules provide the exact redundancy theory and tests.

## Claim status

Locally checked Lean source, not a claim of deployed test removal, measured
performance gains, independent review, or remote publication. Source identity
and validation results accompany the package. No production tests have been
deleted. The repository name is a hypothesis clarified by the exact theorem,
not an assertion of the disproved unrestricted slogan.
