# software-is-incrementally-certifiable

## Release-sequence claim

**Individual admission does not imply release improvement.** This repository
proves conditional sequence guarantees and checked counterexamples to the
unconditional claim. The complete labeled proof / falsification / response
deliverable is [DUET.md](DUET.md).

For the historical two-cost model, adjacent nonregression is necessary and
sufficient for nonregression between every earlier/later pair. Along that chain,
strict endpoint improvement holds exactly when an intervening step is strict.
A separate fixed positive requirement condition prevents behavior deletion.
For the current canonical interface, successful adjacent `releaseLe` checks
yield arbitrary-length all-pairs nonregression, observed-symbol preservation,
and a frontier result relative to the compared history. No theorem asserts
global Pareto optimality without coverage of the declared feasible universe.

The audited pin `f3b9f896ac76a95e7104c98af66e41413e7e5b2d` remains README-only.
The namespace-isolated historical model and exact source pins are documented in
[Legacy/README.md](Legacy/README.md). These sources support the historical
counterexamples; the active interface remains the pinned family dependency.

Lean 4.19.0, core only. `software-is-composable` is required at `476059c25b93679919238ae4293c6b0b4befe486`. `software-optimality` is required at `b52c3170a6e108345bd5ada44ca7355dae55b395`. `software-is-quantifiable` is `430340295c52a015772022b2b663d01120a3a747`, one revision, inherited from those requires. `releaseLe` is `SoftwareIsQuantifiable.Interface.releaseLe`. `certClose` is `Qualification.Derives`.

```sh
./check.sh
```

`./check.sh` discovers and freshly compiles every repository Lean file, treats
warnings as errors, rejects proof escapes, enforces the compiled proof dependency
allowlist, and exercises standing controls and the CLI. The exact contract is
[CHECK_CONTROLS.md](CHECK_CONTROLS.md). Its current receipt and logs are written
under `.lake/all-files-gate/`. The retained `CHECK.log` is historical evidence from
the earlier integration, not the receipt for the new sequence proof.

| Sequence claim | Checked theorem |
|---|---|
| Admission alone implies temporal improvement | Refuted by `Audit.DuetControls.admission_does_not_imply_release_monotonicity` |
| Adjacent two-cost nonregression iff all-pairs nonregression | `LegacySequence.cost_adjacent_iff_global` |
| Endpoint costs strictly improve iff an intervening edge is strict | `LegacySequence.strict_interval_iff` |
| Weak cycle returning to its initial cost is constant throughout | `LegacySequence.return_forces_constant_interval` |
| Existing downward-admission hypotheses propagate admission | `LegacySequence.admitted_sequence` |
| Separately named guard preserves admission, fixed requirements, and cost nonregression | `LegacySequence.guarded_sequence` |
| Historical cost order agrees with the canonical two-cost order | `LegacyBridge.weak_iff_canonical`, `LegacyBridge.strict_iff_canonical` |
| Canonical adjacent comparisons iff all-pairs comparisons | `ReleaseSequence.adjacent_iff_all_pairs` |
| Canonical observed symbols persist without worse readings | `ReleaseSequence.observed_behavior_retained` |
| Later frontiers cover earlier profiles and latest profiles lie on the visited-history frontier | `ReleaseSequence.frontier_covered`, `ReleaseSequence.latest_on_history_frontier` |
| Strict refinement survives weak steps and cannot return | `ReleaseSequence.strict_refinement_persists`, `ReleaseSequence.strict_refinement_no_return` |
| Finite canonical edge checker exactly decides `releaseLe` | `ReleaseSequence.stepCheck_exact`, `ReleaseSequence.checked_sequence` |

The theorem names above are within `IncrementalCert` unless fully qualified.
The new checker is available to callers; the older demonstration CLI retains its
existing admission behavior. Pipeline enforcement is a separate application
obligation, recorded in the duet.

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

`Audit/Counterexamples.lean` remains Lake target `Evidence`; the exhaustive
`./check.sh` gate always checks it, independent of default Lake targets.
`Audit/Refusals.lean` and `Audit/DuetControls.lean` are `Audit` roots. The duet
controls are also imported by the default `IncrementalCert` root.

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

The historical transcript is `CHECK.log`. Current exact-pin verification uses
the receipt and logs described in [CHECK_CONTROLS.md](CHECK_CONTROLS.md).
