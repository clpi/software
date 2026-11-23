# software-is-incrementally-safe

Lean `leanprover/lean4:v4.19.0`. `lake build` uses `-DwarningAsError=true`.

`gate/check.sh` is the check gate: it builds, compiles every tracked `.lean` file with warnings as errors, walks every declaration for axioms (only `propext`, `Quot.sound`, `Classical.choice` allowed; no declared axioms, no unsafe or opaque declarations) and runs an escape scan. `LIMITS.md` says what the theorems below do not prove; read it with the table.

Pins in `lake-manifest.json`, one revision each:

- `software-is-quantifiable` `f370992611d8c722e4897e67dbb8eaecf3d872ed`
- `software-optimality` `16a6c690cf4ec4dedda34328e165da995d7592ae`
- `software-is-composable` `dce6564be7366ae3389e710b53a4623f497290b7`

Composable `dce6564b` and optimality `16a6c690` require the same quantifiable and optimality revisions as the root manifest. `Release` is `SoftwareIsComposable.Release`. `releaseLe` is `SoftwareIsQuantifiable.Interface.releaseLe`. The code cone is `SoftwareIsComposable.InClosure` and `HypergraphIncremental.Affected` (`coneExec_iff_affected`). The ordered-increment cone is `HypergraphIncremental.Affected` over `OrderedIncrement.depGraph`. The C6 profile is `SoftwareIsQuantifiable.Pareto.profileOf` of `outputPoint`, and `outputPoint_eq_iff` shows `outputPoint` keeps the output set. `audit/DependencyModules.lean` proves the removed local cones equivalent to these.

`audit/Counterexamples.lean` is Chris's file, sha256 `3a70977a33e3d28f2cf617214e83363e4cb7298df19418180b226b6384553927`, red commit `677941a67a14066c5319923278ab02803d3da11b`. It is not a default target. `gate/check.sh` requires it to stay red and unchanged (`gate/expected-red.txt`).

`SpecAuthority` is the spec writer's trust: executable allow and label maps, plus the proofs that those maps agree with the propositions and that the trace predicate is prefix-closed. The checker does not derive that trust.

| Claim | Lean | Status |
|---|---|---|
| F1 ordered prefix-closed safety | `f1_releaseSafe_distinguishes`, `door_is_prefixClosed` | proven |
| F2 profile taint cannot see a two-run leak | `same_profile`, `f2_two_run` | proven |
| F3 external context, config, and data edges | `f3_external_uses_closureHyp` | premise |
| F3 computed code cone covers the inductive cone | `closure_from_release`, `coneExec_complete`, `coneExec_iff_affected` | proven |
| F4 accept implies `ReleaseSafe` and `TaintFree` | `f4_checker_sound`, `incremental_release_safe` | proven |
| F5 empty behavior is not `ReleaseSafe` | `nothing_refused`, `empty_behaviors_refused`, `c4_abstract` | proven |
| C1 omitted dependency edge | `c1_omitted_dep_refused` | proven |
| C2 unlabeled high observation | `c2_unlabeled_leak_refused` | proven |
| C3 raised submitter budget | `c3_budget_raised_refused` | proven |
| C4 nothing is not safe | `nothing_refused` | proven |
| C5 order-blind allow-list is not acceptance | `allowedTrace_swap`, `c5_swap_does_not_yield_releaseSafe` | proven |
| C6 two-run leak is refused; profile limit remains | `leak_not_releaseSafe`, `same_profile`, `outputPoint_eq_iff` | proven |
| Submitter deps, labels, and budgets do not change `check` | `check_submitter_invariant` | proven |
| Admitted cost does not leave the previous cost point | `accept_cost_noWorse` | proven |
| Spec writer's trace and event authority | `SpecAuthority` | premise |
| An unguarded Pareto frontier is not a release gate | `Optimality.paretoMaximal_can_regress` | disproven |
| Overlapping cost bounds are not per-execution dominance | `Optimality.not_per_execution_dominance` | disproven |

`accept_cost_noWorse` is `Optimality.noWorse` of the checked cost against the spec bounds: the admitted point does not leave the incumbent on either axis. `Optimality.guardedMaximal` is that guard followed by the Pareto filter. `Optimality.paretoMaximal_can_regress` shows the filter alone can leave an axis.
