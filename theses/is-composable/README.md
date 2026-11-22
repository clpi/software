# software-is-composable

Machine-checked statements about release admission and composition, with explicit
model boundaries. Lean 4.19.0. This repository contains the finite per-symbol
admission model, the exact audited subset/refinement module under `Legacy`, and
a strengthened `Interaction` model in which individually safe components can
generate an unsafe observation together.

**The name is not an unconditional theorem about arbitrary software.** Read the
[proves/cannot-say statement and premise ledger](docs/composability-audit.md),
[independent counterexample review](docs/independent-interaction-review.md), and
[verification receipt](docs/verification.md).

```sh
./check.sh
```

The gate discovers and freshly compiles every repository Lean source, including
audit and example files, with warnings as errors. It rejects admitted proofs,
custom logical axioms, source escapes and unapproved elaboration hooks, audits
compiled axiom dependencies, and exercises standing negative controls plus the
existing harness and examples. Standard Lean foundational axioms are reported
separately from compiler-generated runtime implementation constants.
The current run writes `.lake/all-files-gate/receipt.json` and adjacent logs.
`CHECK.log` is a historical pre-audit transcript, not evidence for the new head.

## Composition and emergent interaction

`Legacy.incremental_monotone` proves pointwise subset refinement from the same
condition on changed components. Its dependency composition only propagates
observations already present in a component profile. `Interaction` adds one
positive binary rule: two derivable observations may produce a third.

The independent controls prove that two isolated safe component closures can
jointly produce a forbidden `alarm`. Refinement monotonicity still holds for
fixed rules and dependencies, and more generally when those relations shrink
or their new constructors can be simulated in the old closure. Safety of all
locally safe assignments holds exactly when the common allowed set is closed
under the interaction rules (on a nonempty component domain). An already safe
composed baseline can instead be preserved without that universal closure
premise.

| Claim | Theorem / standing control | Status |
|---|---|---|
| Legacy pointwise update refinement is exactly the changed-component hypothesis | `Interaction.incremental_monotone_iff` | PROVEN; local refinement remains a PREMISE |
| Legacy composition cannot create observations without a component origin | `Interaction.legacy_has_origin` | PROVEN; model restriction |
| No interaction rules recovers the exact legacy reachability relation | `Interaction.no_interaction_iff_legacy` | PROVEN |
| Positive interactions preserve refinement of bases, rules and dependencies | `Interaction.reaches_refinement`, `incremental_interactions_monotone` | PROVEN |
| New rules can be admitted if old derivations simulate them | `Interaction.reaches_simulation`, `safe_of_simulation` | PROVEN under explicit primitive simulation PREMISES |
| All locally safe assignments compose safely exactly when the allowed set is interaction-closed | `Interaction.universal_safety_iff_closed` | PROVEN; specification closure remains a PREMISE |
| Particular safe composed baselines stay safe under refinement without universal specification closure | `Interaction.safe_of_refinement`, `safe_of_incremental` | PROVEN |
| Rechecking the change cone equals a full recheck in a fixed interaction context | `Interaction.incremental_recheck_iff` | PROVEN under safe baseline and fixed-context PREMISES |
| Independently safe components always compose safely | `Audit/InteractionControls.lean` | DISPROVEN |
| Local refinement suffices with arbitrary context changes or absence-sensitive interactions | `Audit/InteractionControls.lean` | DISPROVEN |
| Real programs / the admission CLI implement these abstract interactions | P-MODEL-ADEQUACY, P-EXECUTABLE-BRIDGE | OPEN PREMISES |

The new theorem's subset order and the finite model's qualified-behavior
retention order below are different contracts. Neither is renamed into the
other. The new interaction model is available through the stable import; the
existing CSV admission harness does not evaluate it.

## Stable import

`import SoftwareIsComposable`

| Name | Role |
|---|---|
| `SymbolProfile`, `Release` | Per-symbol behaviors and cost bounds |
| `releaseAdmitted`, `ReleaseAdmitted`, `releaseAdmitted_iff` | Step admission, Bool and Prop |
| `releaseAdmitted_trans` | Admission composes along a chain |
| `InteractionClosed`, `moduleAdmission_compose` | Module composition under the side condition |
| `evidence_remaining` | Independent prefix observations leave `2^free` candidates |
| `symbolVerdict`, `symbolVerdicts` | Executable per-symbol verdict. `symbolVerdict_admitted_iff` proves the admitted case is `symbolAdmitted` |

## Existing finite admission claims

| Claim | Theorem | Status |
|---|---|---|
| Finite schedule space | `scheduleSpace_finite` | PROVEN |
| Admission is the symbol-wise behavior and bound check | `releaseAdmitted_iff`, `symbolVerdict_admitted_iff` | PROVEN |
| Qualified behaviors are kept on an admitted step | `qualifiedMono` | PROVEN |
| That inclusion composes along admitted steps | `qualifiedTrans`, `releaseAdmitted_trans` | PROVEN |
| Cost upper bounds do not regress, and the bound vector is not strictly Pareto-dominated | `costNoRegression`, `costTrans` | PROVEN |
| A bound-admitted step is no worse on every execution | `not_per_execution` | DISPROVEN |
| Per-module admission implies whole-release admission when calls stay inside a module | `moduleAdmission_compose` (`InteractionClosed`) | PROVEN |
| The same implication with a cross-module call and a stubbed callee | `moduleAdmission_counterexample` | DISPROVEN |
| Fixing a prefix of independent bits leaves `2` to the number of free bits | `evidence_remaining` | PROVEN |
| A repeated observation of the same bit shrinks the set again | `not_repeated_observation_shrinks` | DISPROVEN |
| One disqualifying bit leaves no candidates | `not_disqualification_empties` | DISPROVEN |
| A total observation of all `n` symbols leaves one candidate | `determined_of_coverage` | PREMISE (`SymbolCoverage`) |
| Caller closure is the hypergraph affected set of an unchanged call edge set | `inClosure_iff_affected` | PROVEN |
| Rechecking that affected set matches a full recheck when profiles outside it are unchanged | `incrementalRecheck_iff` | PROVEN |
| Rechecking only the edited symbol matches a full recheck | `not_recheck_seed_only` | DISPROVEN |
| The worked example's regressed symbol is refused | `worse_refused` | PROVEN |

software-is-quantifiable is required at `d88acbdc3ba78fff994067d2c73bcc01622b3f61`. software-optimality is required from git at `ec1eadda0a29d1b254a98feb5ad24911a095c454`; its default branch is `master`. That optimality commit requires quantifiable `f370992611d8c722e4897e67dbb8eaecf3d872ed`; the root requirement above selects `d88acbdc3ba78fff994067d2c73bcc01622b3f61`. `Qualification`, `ExecutableClosure`, `FiniteFrontier`, `FiniteQualification`, and `HypergraphIncremental` are that package's modules. The copy of `FiniteFrontier` previously kept in this repository was a prefix of the upstream file and declared nothing the upstream file does not declare.

`priorOf` and `submissionOf` send one composable symbol's behavior list to `PriorQualification` and `BehaviorSubmission`. `oneSymbol` is that one-symbol agreement with `acceptsRelease`. `nothing_below` records that `Interface.releaseLe` holds for the empty release, and that `admittedBySpec` refuses an empty submission.

## Harness

`lake exe harness old.csv new.csv` reads

```
id,behaviors,costs
1,0 1,0:2 1:4
```

Costs are space-separated `lo:hi` bounds. For each symbol in the old file it prints `ADMITTED` or `REFUSED` with `missing_symbol`, `behavior_dropped`, `cost_regressed`, `axis_mismatch`, or `invalid_bounds`. The decision is `symbolVerdicts`.

`examples/old.csv` and `examples/new.csv` keep symbol 1 and refuse symbol 7 because its upper bound rises from 4 to 9:

```
1 ADMITTED
7 REFUSED cost_regressed 0
```

## Implications

`Implications.lean` writes each listed headline as `theorem from upstream
declarations + local lemmas`. `./check.sh` runs it and records the generated
report in `build/implications.md`, with checker output in
`.lake/all-files-gate/implications.log`. The generator is the source of that
list; `CHECK.log` remains historical.

## Controls

The gate keeps the prior admitted-proof and false-release controls, exercises
all-file inventory and proof-escape refusals, and compiles the independent
interaction controls in `Audit/InteractionControls.lean`. See
[controls/README.md](controls/README.md) for the gate controls and trust boundary.
