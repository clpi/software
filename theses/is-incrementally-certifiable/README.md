# software-is-incrementally-certifiable

Lean 4.19.0, core only. `software-is-composable` is required at `476059c25b93679919238ae4293c6b0b4befe486`. `software-optimality` is required at `b52c3170a6e108345bd5ada44ca7355dae55b395`. `software-is-quantifiable` is `430340295c52a015772022b2b663d01120a3a747`, one revision, inherited from those requires. `releaseLe` is `SoftwareIsQuantifiable.Interface.releaseLe`. `certClose` is `Qualification.Derives`.

```sh
./check.sh
```

`./check.sh` refuses `sorry`, `admit`, `axiom`, and `native_decide`, treats warnings as errors, prints axiom dependencies, and runs the CLI. The transcript is `CHECK.log`.

## Premises

| Name | Statement |
|---|---|
| `RequiredNonempty` | `requiredOf prev ≠ []`. `requiredOf` is `(priorOf prev).qualified`. |
| `NothingOutside` | A list of points and a catalogue contain the same points. |
| `NoCoverageGaps` | `Optimality.GeneratorCoverage`: every intended point is in the catalogue, and every catalogue point is intended. |
| `IndependencePremise` | The indices in `evidence_cuts` are distinct and in range. |
| `CoveragePremise` | Every symbol index occurs. |

## Claims

| Claim | Theorem | Status |
|---|---|---|
| `B a` implies `certClose B R a` | `extensive` | PROVEN |
| `B` and `R` pointwise below `C` and `S` implies `certClose B R` below `certClose C S` | `monotone` | PROVEN |
| `certClose (certClose B R) R a ↔ certClose B R a` | `idempotent` | PROVEN |
| `certClose (B ∪ C) R a ↔ certClose (certClose B R ∪ certClose C R) R a` | `compounding` | PROVEN |
| That identity is membership in `certClose B R` or `certClose C R` | `compounding_not_pointwise_union` | DISPROVEN |
| `consistentLength n fix * pow2 fix.length = pow2 n` | `evidence_cuts` | PROVEN |
| `IndependencePremise` | `evidence_cuts` | PREMISE |
| `2 * consistentLength 1 [(0, true), (0, true)] = pow2 1` | `duplicate_does_not_cut` | DISPROVEN |
| `consistentLength n fix = 1` | `consistent_singleton_of_coverage` | PROVEN |
| `CoveragePremise` | `consistent_singleton_of_coverage` | PREMISE |
| `fix.length < n` implies `consistentLength n fix = 1` | `partial_not_singleton` | DISPROVEN |
| `requiredOf prev = (priorOf prev).qualified` | `required_is_prior` | PROVEN |
| `allowedOf spec = spec.allowed` | `allowed_is_spec` | PROVEN |
| `check { spec with required := req } prev d = check spec prev d` | `check_ignores_spec_required` | PROVEN |
| `accepted specBudget prevNeed [("app", [])] = false` | `empty_behaviors_refused` | PROVEN |
| `check` of `specBudget` with `required := []`, `budgetDelta` with `changed := [("app", [])]` and `submittedRequired := []`, equals `refuse "app"` | `spec_required_empty_still_refused` | PROVEN |
| `d1.changed = d2.changed` implies `check spec prev d1 = check spec prev d2` | `check_submitter_invariant` | PROVEN |
| `check spec prev d = accept` implies `ReleasePred spec prev d.changed` | `check_sound` | PROVEN |
| The two `behaviorAfter` pairs on `baseNeed` are equal | `incremental_eq_scratch` | PROVEN |
| `combinedAdmission allowed prior behaviors = true` iff `prior.qualified ≠ []`, `noQualifiedBehaviorLost`, and `releaseLE` | `combined_iff` | PROVEN |
| `releaseLE [1] [1, 2] = true` | `feature_add_fails_releaseLE` | DISPROVEN |
| `noQualifiedBehaviorLost` of qualified `[1]` and offered `[]` is true | `removal_fails_acceptsRelease` | DISPROVEN |
| `noQualifiedBehaviorLost` of qualified `[]` and offered `[]` is false | `empty_required_passes_c4` | DISPROVEN |
| On `StepAdmitted [c, b, a]`, with `RequiredNonempty`, `requiredOf = prior.qualified`, `NothingOutside`, and `NoCoverageGaps`, `¬ Optimality.dominates` for `a` over `c`, `b` over `c`, and `a` over `b`; `Optimality.dominates a c` agrees with `Interface.dominates` on `Pareto.costSpace` by `local_dominates_iff_canonical`; `c ∈ paretoMaximal catalogue`; no intended point dominates `c`; `requiredOf prev ≠ []` | `pareto_monotone_chain` | PROVEN |
| `NothingOutside` | `pareto_monotone_chain` | PREMISE |
| `NoCoverageGaps` | `pareto_monotone_chain` | PREMISE |
| `RequiredNonempty` | `pareto_monotone_chain` | PREMISE |
| `(2, 2)` on the frontier of `[(2, 2)]` is undominated by `(0, 0)` | `outside_dominates` | DISPROVEN |
| `(1, 1)` on the frontier of `[(1, 1)]` is undominated by intended `(0, 0)` | `coverage_gap_dominates` | DISPROVEN |
| `releaseLe selectedSpace` holds for readings `[9, 100]` against `[10, 1]` | `axes_change_hides_regression` | DISPROVEN |
| `∀ x y, (1 ≤ x ≤ 100) → (2 ≤ y ≤ 3) → y < x` on the first coordinate, second coordinate `0` | `not_per_execution` | DISPROVEN |
| `check specLeak prevLib omitDelta = refuse "app"` | `omitted_refused` | PROVEN |
| `check specLabel prevLib` of `omitDelta` with `obsHigh := noObsHigh` equals `refuse "app"` | `leak_unlabeled_refused` | PROVEN |
| `check specBudget prevNeed budgetDelta = refuse "app"` | `budget_raised_refused` | PROVEN |
| `check specBudget prevNeed` of `budgetDelta` with `changed := [("app", ["a"])]` and `submittedRequired := []` equals `refuse "app"` | `submitted_required_still_refused` | PROVEN |
| `HoldsRequired required nothing` when some observation is required | `nothing_refused` | DISPROVEN |
| `allowedTrace` distinguishes `List.Perm` traces | `unordered_traces` | DISPROVEN |
| `flowBeh` determines `Reaches` of `"secret"` from `"app"` | `profile_cannot_see_flow` | DISPROVEN |

`Audit/Counterexamples.lean` is Lake target `Evidence`, checked at `d094a2e32fd89e55fcdd879941e9feb1011bf50c`. It is not a default target. Its theorems are `c1_omitted_edge_accepts`, `c2_label_hides_leak`, `c3_raised_budget_accepts`, `c4_nothing_safe`, `c4_nothing_ni`, and `c4_releaseLE_nothing`. `Audit/Refusals.lean` is the `Audit` root.

## Implications

`Implications.lean` prints `THEOREM`, `upstream:`, and `local:` for each headline. `./check.sh` runs it. The lines are in `CHECK.log`.

## CLI

`lake env lean --run Cli.lean examples/chain.json` prints:

```
release-zero: accept
release-one: refused app
release-two: not-applied
```

## Build log

`./check.sh` exit 0. The transcript is `CHECK.log`.
