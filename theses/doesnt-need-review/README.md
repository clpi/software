# software-doesnt-need-review

Lean 4.19.0, core only (`lean-toolchain`). `./check.sh` builds with warnings as errors, refuses `sorry`, `admit`, and custom axioms, prints `#print axioms` for the headline theorems, and checks the generated upstream-dependency listing.

`software-is-composable` is required from git at `033c12c01299a9b28983bee410c230641adc7d1e`. Admission is the imported `symbolAdmitted`, `releaseAdmitted`, `symbolVerdict`, and `accepts`. `scripts/UpstreamDeps.lean` prints each headline and the `Chain` or `SoftwareIsComposable` declarations it uses. `check.sh` checks that listing. It is not copied here.

The require pulls `software-is-quantifiable` at `37917a4195efb1d0423a422ee954d767a9be1cd3` (Lean 4.15.0). That pin's `Coverage` module is not imported. Ledger coverage stays the local `Chain.Quantifiable` stand-in. `software-optimality` has no lakefile. Local definitions remain for certifiable, regress, and safe, each with an equivalence to the imported admission.

| Local | Equivalence | State |
|---|---|---|
| `Chain.Quantifiable.PlatformPremise`, `coverage`, `recorded`, `missing`, `unrestricted_witness` | ledger form of coverage; not the imported 4.15.0 `Coverage` | quantifiable main is past this pin; the required commit does not typecheck `Coverage` here |
| `Chain.Optimality.acceptsGuarded` | shape of guarded admission: same context, no dropped behavior, `noWorse` | `software-optimality` `master` `af23f5d27990c84ac392c156f4bef61f61b64767` has no lakefile |
| `Chain.Certifiable.extensive`, `growBehaviors` | `extensive_equiv`: growing an already-present behavior list does not change `symbolAdmitted` | `software-is-incrementally-certifiable` not merged |
| `Chain.Regress.verdict`, `behaviorRegressed`, `costRegressed` | `regress_equiv`: under matching id, valid bounds, and equal cost length, regression ↔ `symbolAdmitted = false` | `software-doesnt-have-to-regress` not merged |
| `Chain.Safe.verdict`, `preserved` | `safe_equiv`: behavior preservation ↔ imported `accepts` | `software-is-incrementally-safe` not merged |

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
| A dropped behavior is not `symbolAdmitted` (`bad_cell_not_qualified`) | PROVEN |
| A bad cell the certifier does not watch is missed by the certifier and caught by outside knowledge (`boundary_missed_by_certifier`, `residual_unwatched_cell`, `outside_not_through_facts`) | PROVEN |
| An identifier witness is ledger coverage | DISPROVEN (`unrestricted_witness` together with `boundary_legacy_witness_insufficient`) |
| The boundary certifier mediates its roster | DISPROVEN (`boundary_no_platform_premise`) |
| Coverage: every roster execution is a validated ledger record | PREMISE (`coverage` takes `PlatformPremise`). Not implied by an identifier witness |
| The watched axes are the intended axes, and every intended cell is observed | PREMISE (`SpecRight`, `CellsObserved`) |
| Given `SpecRight` and `CellsObserved`, a bad intended cell is refused (`redundant_under_premises`). This does not discharge `PlatformPremise` | PROVEN |
| Elimination of manual review | PROPOSAL. It rests on the spec premise, the coverage premise, and on the criterion being a decidable profile predicate. See PROPOSAL.md |
| Human review collapses into rubber stamping in practice | UNMEASURED |

`#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`, or no axioms. `profile_space_finite` and `decided_on_finite_space` use the first three. `coverage` uses none: it is the projection of `PlatformPremise`.
