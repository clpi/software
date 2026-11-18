# software-is-composable

Machine-checked incremental release admission for per-symbol behavior profiles. Lean 4.19.0, core only. `./check.sh` refuses `sorry`, `admit`, `axiom`, and `native_decide`, treats warnings as errors, prints axiom dependencies, runs two negative controls, and runs the harness.

```sh
./check.sh
```

The transcript is `CHECK.log`. On Lean 4.19.0 (commit `6caaee842e94`) the recorded run exits 0. Headline axioms are only `propext`, `Classical.choice`, and `Quot.sound`, or none. `sorryAx` does not appear.

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

## Claims

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

`Implications.lean` writes each headline as `theorem from upstream declarations + local lemmas`. `./check.sh` runs it and records the lines in `CHECK.log`. The generator is the source of that list.

## Controls

`check.sh` rejects a scratch proof that uses `sorry`, then rejects a proof that the regressed example is `releaseAdmitted`, then accepts this tree.
