# software-is-incrementally-safe

Lean `leanprover/lean4:v4.19.0`. `lake build` uses `-DwarningAsError=true`.

Pins in `lake-manifest.json`, one revision each:

- `software-is-quantifiable` `430340295c52a015772022b2b663d01120a3a747`
- `software-optimality` `b52c3170a6e108345bd5ada44ca7355dae55b395`
- `software-is-composable` `033c12c01299a9b28983bee410c230641adc7d1e`

Composable's own manifest pins quantifiable `37917a4195efb1d0423a422ee954d767a9be1cd3`. The root manifest keeps `430340295c52a015772022b2b663d01120a3a747`. Optimality `b52c3170` requires that same quantifiable revision. `Release` is `SoftwareIsComposable.Release`. `releaseLe` is `SoftwareIsQuantifiable.Interface.releaseLe`.

`audit/Counterexamples.lean` is Chris's file, sha256 `3a70977a33e3d28f2cf617214e83363e4cb7298df19418180b226b6384553927`, red commit `677941a67a14066c5319923278ab02803d3da11b`. It is not a default target.

`SpecAuthority` is the spec writer's trust: executable allow and label maps, plus the proofs that those maps agree with the propositions and that the trace predicate is prefix-closed. The checker does not derive that trust.

| Claim | Lean | Status |
|---|---|---|
| F1 ordered prefix-closed safety | `f1_releaseSafe_distinguishes`, `door_is_prefixClosed` | proven |
| F2 profile taint cannot see a two-run leak | `same_profile`, `f2_two_run` | proven |
| F3 external context, config, and data edges | `f3_external_uses_closureHyp` | premise |
| F3 computed code cone covers the inductive cone | `closure_from_release`, `coneExec_complete` | proven |
| F4 accept implies `ReleaseSafe` and `TaintFree` | `f4_checker_sound`, `incremental_release_safe` | proven |
| F5 empty behavior is not `ReleaseSafe` | `nothing_refused`, `empty_behaviors_refused`, `c4_abstract` | proven |
| C1 omitted dependency edge | `c1_omitted_dep_refused` | proven |
| C2 unlabeled high observation | `c2_unlabeled_leak_refused` | proven |
| C3 raised submitter budget | `c3_budget_raised_refused` | proven |
| C4 nothing is not safe | `nothing_refused` | proven |
| C5 order-blind allow-list is not acceptance | `allowedTrace_swap`, `c5_swap_does_not_yield_releaseSafe` | proven |
| C6 two-run leak is refused; profile limit remains | `leak_not_releaseSafe`, `same_profile` | proven |
| Submitter deps, labels, and budgets do not change `check` | `check_submitter_invariant` | proven |
| Admitted cost does not leave the previous cost point | `accept_cost_noWorse` | proven |
| Spec writer's trace and event authority | `SpecAuthority` | premise |
| An unguarded Pareto frontier is not a release gate | `Optimality.paretoMaximal_can_regress` | disproven |
| Overlapping cost bounds are not per-execution dominance | `Optimality.not_per_execution_dominance` | disproven |

`accept_cost_noWorse` is `Optimality.noWorse` of the checked cost against the spec bounds: the admitted point does not leave the incumbent on either axis. `Optimality.guardedMaximal` is that guard followed by the Pareto filter. `Optimality.paretoMaximal_can_regress` shows the filter alone can leave an axis.

Build evidence for this head is pending an independent rebuild by Tools.
