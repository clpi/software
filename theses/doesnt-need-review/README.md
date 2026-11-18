# software-doesnt-need-review

Lean 4.19.0, core only (`lean-toolchain`). `./check.sh` builds with warnings as errors, refuses `sorry`, `admit`, and custom axioms, prints `#print axioms` for the headline theorems, and checks the generated upstream-dependency listing.

Upstream packages are not `require`d. `software-is-quantifiable` is on `main` at `ba27febf48c85bccaaccbace7cc3faba5eff879c` with toolchain `leanprover/lean4:v4.15.0`, so a require does not build under this pin. The others are not libraries on `main`. Local names under `Chain` are the stand-ins. `scripts/UpstreamDeps.lean` prints each headline and the `Chain` declarations it uses. `check.sh` checks that listing. It is not copied here.

| Local | Corresponds to | State |
|---|---|---|
| `Chain.Quantifiable.PlatformPremise`, `coverage`, `recorded`, `missing`, `unrestricted_witness`, `Witnessed` | `SoftwareIsQuantifiable.Coverage` of the same names | on `main` at `ba27febf48c85bccaaccbace7cc3faba5eff879c`, toolchain v4.15.0 |
| `Chain.Optimality.acceptsGuarded` | shape of `SoftwareIsQuantifiable.Pareto.acceptsRelease`: same context, no dropped behavior, `noWorse` | quantifiable as above. `software-optimality` is on `master` at `af23f5d27990c84ac392c156f4bef61f61b64767`, Lean 4.19.0, no lakefile, not branch `main` |
| `Chain.Composable.qualified` | per-symbol profile qualification | `software-is-composable` `main` `929d8e355857b6557c1b5d1a6bd505d9bdaeea7f` has no package |
| `Chain.Certifiable.extensive` | extensivity of a certifier | `software-is-incrementally-certifiable` `master` `f3b9f896ac76a95e7104c98af66e41413e7e5b2d` is a README, not `main` |
| `Chain.Regress.verdict` | refusal by symbol on a per-symbol regression | `software-doesnt-have-to-regress` `master` `24d36c13414867e59ae67ccf47f83cc250ce55af` is a README, not `main` |
| `Chain.Safe.verdict` | refusal by symbol on a safety axis | `software-is-incrementally-safe` `master` `9466135815aa80e714d2a6999fd0aa8807375ff3` has no package, not `main` |

## Claims

| Claim | Status |
|---|---|
| If a reviewer's acceptance is a function of the certified facts, the releases consistent with those facts are the same with and without the review (`zero_information`) | PROVEN |
| Under that factoring, a reviewer that does not approve a certifier refusal either agrees with the certifier on the fact class or rejects the whole class, a pure veto with no finer criterion (`agrees_or_pure_veto`, `constant_reject_is_veto`) | PROVEN |
| A decidable predicate on the finite per-symbol profile is a total certifier axis and is the row of a table of size `2^n` (`profile_space_finite`, `decided_on_finite_space`, `profile_criterion_mechanizable`) | PROVEN |
| Mechanization for an arbitrary semantic property of a program | not claimed |
| Non-trivial semantic properties of programs are undecidable in general, so they are not total certifier axes. They stay human, a named spec premise, or a decidable profile approximation whose gap stays named (`semantic_not_total_axis`, `approx_keeps_gap`). Rice, H. G., Classes of recursively enumerable sets and their decision problems, Transactions of the American Mathematical Society 74 (1953), 358–366. Not formalized | LIMIT |
| Once a profile axis is installed, extension does not drop it (`process_monotone`, `criterion_never_lost`, from `Chain.Certifiable.extensive`) | PROVEN |
| The disposition process terminates on a finite criterion list (`process_terminates`) | PROVEN |
| A bad cell the certifier does not watch is missed by the certifier and caught by outside knowledge (`boundary_missed_by_certifier`, `residual_unwatched_cell`, `outside_not_through_facts`) | PROVEN |
| An identifier witness is ledger coverage | DISPROVEN (`unrestricted_witness` together with `boundary_legacy_witness_insufficient`) |
| The boundary certifier mediates its roster | DISPROVEN (`boundary_no_platform_premise`) |
| Coverage: every roster execution is a validated ledger record | PREMISE (`coverage` takes `PlatformPremise`). Not implied by an identifier witness |
| The watched axes are the intended axes, and every intended cell is observed | PREMISE (`SpecRight`, `CellsObserved`) |
| Given `SpecRight` and `CellsObserved`, a bad intended cell is refused (`redundant_under_premises`). This does not discharge `PlatformPremise` | PROVEN |
| Elimination of manual review | PROPOSAL. It rests on the spec premise, the coverage premise, and on the criterion being a decidable profile predicate. See PROPOSAL.md |
| Human review collapses into rubber stamping in practice | UNMEASURED |

`#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`, or no axioms. `profile_space_finite` and `decided_on_finite_space` use the first three. `coverage` uses none: it is the projection of `PlatformPremise`.
