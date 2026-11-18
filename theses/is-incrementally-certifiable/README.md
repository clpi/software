# software-is-incrementally-certifiable

Lean 4.19.0, core only. `software-is-quantifiable` is required at `430340295c52a015772022b2b663d01120a3a747`. `software-is-composable` is required at `033c12c01299a9b28983bee410c230641adc7d1e`. The manifest lists one revision of each. `Release` is `SoftwareIsQuantifiable.Interface.Release`. `certClose` is `Qualification.Derives`. `./check.sh` refuses `sorry`, `admit`, `axiom`, and `native_decide`, treats warnings as errors, prints axiom dependencies, and runs the CLI. `Coverage.lean` is not imported.

```sh
./check.sh
```

The recorded run is `CHECK.log`. Headline dependencies are `propext`, `Classical.choice`, and `Quot.sound`, or none.

`cert : Certificate → Delta → Option Certificate` reads `d.changed` and the certificate's spec and previous release. `check_submitter_invariant` states that equal `changed` fields give equal verdicts.

## Premises

| Name | Role |
|---|---|
| `RequiredNonempty` | `requiredOf` is `PriorQualification.qualified` from the previous release. `accepted` is false when that list is empty. |
| `IndependencePremise` | The `k` observations in `evidence_cuts` are distinct indices in range. |
| `CoveragePremise` | Every symbol index occurs. Used only by `consistent_singleton_of_coverage`. |
| `FixedSelectedAxes` | Each release in the chain has symbol id 0 and two cost axes. |
| `ValidMeasurements` | Every cost bound on the chain satisfies `lo ≤ hi`. |
| `BaselineEligible` | The first release has a symbol, and its bounds satisfy `lo ≤ hi`. |

`requiredOf` is the previous release's `qualified` list. `allowedOf` is `spec.allowed`. Neither reads `Delta.submittedRequired`, `Delta.submittedAllowed`, `Delta.deps`, `Delta.obsHigh`, `Delta.symHigh`, `Delta.boundTime`, `Delta.boundCompute`, or `Spec.required`.

## Claims

| Claim | Theorem | Status |
|---|---|---|
| `X ⊆ certClose X` | `extensive` | PROVEN |
| `X ⊆ Y` implies `certClose X ⊆ certClose Y` | `monotone` | PROVEN |
| `certClose (certClose X) = certClose X` | `idempotent` | PROVEN |
| `certClose (B ∪ D) = certClose (certClose B ∪ certClose D)`, from `Qualification.compounding` | `compounding` | PROVEN |
| That identity is pointwise union | `compounding_not_pointwise_union` | DISPROVEN |
| `k` distinct binary observations cut the release space by `2^k` | `evidence_cuts` | PROVEN under `IndependencePremise` |
| Repeating an observation cuts by `2^k` for `k` copies | `duplicate_does_not_cut` | DISPROVEN |
| Observing every symbol leaves one release | `consistent_singleton_of_coverage` | PREMISE `CoveragePremise` |
| A proper subset of observations leaves one release | `partial_not_singleton` | DISPROVEN |
| `requiredOf` is the previous `PriorQualification.qualified` | `required_is_prior` | PROVEN |
| `allowedOf` is `spec.allowed` | `allowed_is_spec` | PROVEN |
| Changing `Spec.required` changes `check` | `check_ignores_spec_required` | DISPROVEN |
| The empty behavior list is accepted when the previous qualified list is `["need"]` | `empty_behaviors_refused` | DISPROVEN |
| `Spec.required = []` and `submittedRequired = []` accept a dropped `need` | `spec_required_empty_still_refused` | The verdict is `refuse "app"` |
| `check` depends on the submitted behavior list only | `check_submitter_invariant` | PROVEN |
| `check = accept` implies `ReleasePred` | `check_sound` | PROVEN |
| Two disjoint behavior writes match one concatenated write | `incremental_eq_scratch` | PROVEN |
| On a chain `c, b, a` with each step `releaseLe`, an earlier release does not `releaseDominates` a later one | `pareto_monotone_chain` | PROVEN under `FixedSelectedAxes`, `ValidMeasurements`, `BaselineEligible` |
| Keeping both axes, the step from highs `(10, 1)` to `(9, 100)` is admitted | `axes_change_hides_regression` | DISPROVEN. The one-axis check `axesOf [0]` accepts that step |
| Upper bounds `[2, 3]` against `[1, 100]` dominate every in-bound pair | `not_per_execution` | DISPROVEN |
| `combinedAdmission` is `releaseLE` and `acceptsRelease` | `combined_iff` | PROVEN |
| Behaviors `[1, 2]` satisfy `releaseLE` against allowed `[1]` | `feature_add_fails_releaseLE` | DISPROVEN. `acceptsRelease [1]` holds |
| Behaviors `[]` satisfy `acceptsRelease` against required `[1]` | `removal_fails_acceptsRelease` | DISPROVEN. `releaseLE [1, 2]` holds |
| Required `[]` fails `acceptsRelease [] []` | `empty_required_passes_c4` | DISPROVEN |
| Omitting edge `app → lib` from the delta accepts the leak | `omitted_refused` | The verdict is `refuse "app"` |
| Setting the delta's `obsHigh` to false accepts the leak | `leak_unlabeled_refused` | The verdict is `refuse "app"` |
| Raising the delta budget accepts cost 4 against spec budget 1 | `budget_raised_refused` | The verdict is `refuse "app"` |
| Submitting `submittedRequired = []` and dropping `need` accepts | `submitted_required_still_refused` | The verdict is `refuse "app"` |
| `HoldsRequired` holds of `nothing` when some observation is required | `nothing_refused` | DISPROVEN |
| Allowed traces distinguish order | `unordered_traces` | The predicate is `List.Perm`-invariant |
| A profile determines `Reaches` | `profile_cannot_see_flow` | DISPROVEN. The same `flowBeh` reaches `"secret"` under `flowDeps` and not under `noDeps` |

`pareto_monotone_chain` uses `SoftwareIsQuantifiable.Interface.releaseLe_trans`. It does not use `extensive`.

`Audit/Counterexamples.lean` is the red baseline, checked at `d094a2e32fd89e55fcdd879941e9feb1011bf50c`. Its theorems `c1_omitted_edge_accepts`, `c2_label_hides_leak`, `c3_raised_budget_accepts`, `c4_nothing_safe`, `c4_nothing_ni`, and `c4_releaseLE_nothing` are proved for the checker in that file, which reads `deps`, `obsHigh`, and the budget from the delta. Lake target `Evidence` roots that file. It is not a default target. `Audit/Refusals.lean` is the `Audit` root.

## Implications

`Implications.lean` prints each headline as `THEOREM`, `upstream:`, and `local:`. `./check.sh` runs it. The lines are in `CHECK.log`.

## CLI

`lake env lean --run Cli.lean examples/chain.json` runs `cert` on three releases. The middle release drops `need`.

```
release-zero: accept
release-one: refused app
release-two: not-applied
```

## Build log

`./check.sh` exit 0. The transcript is `CHECK.log`.
