# software-doesnt-have-to-regress

Lean 4.19.0, core only. `./check.sh` refuses `sorry`, `admit`, `axiom`, and `native_decide`, treats warnings as errors, prints axiom dependencies, runs the negative controls, and runs `gate` on `examples/stream.json`. The transcript is `CHECK.log`.

Pinned inputs:

- `software-is-quantifiable` `9f5ca06c0d5d92904f8509af676ab09ea5e0d79c`, module `SoftwareIsQuantifiable.Pareto`
- `software-is-composable` `033c12c01299a9b28983bee410c230641adc7d1e` (`033c12c0`). This environment cannot clone that private repository. `vendor/software-is-composable` is `Profile.lean` and `Admission.lean` from that commit. `REVISION` is the commit. `check.sh` checks it.

`behaviorsKept_eq_composable` is `behaviorsKept = SoftwareIsComposable.accepts`. `composable_hi_of_boundsNoWorse` sends a both-endpoint `boundsNoWorse` step to that repository's upper-bound inequality. `accepts` here also requires a strict gain, so it is not `symbolAdmitted`.

`software-frontier-is-solvable` proves `guarded_no_regression` and `guarded_frontier_exists` for a cost function on every index, assuming the baseline stays eligible. Those theorems do not take a named axis list or a measurement-validity premise. The two theorems below do.

## Claims

| Claim | Theorem | Status |
|---|---|---|
| On the selected axes, an eligible baseline with consistent interval measurements is no worse than itself, including on every authorized axis | `baseline_is_witness` | PROVEN from `BaselineStaysEligible`, `AxesRight`, `MeasurementsValid` |
| `select` returns the baseline or the first guarded candidate. On every authorized axis that result's upper bound is ≤ the baseline, the baseline interval stays consistent, and the baseline predicate stays true | `select_never_regresses` | PROVEN from the same three premises |
| If that baseline is also in the candidate list, it is in the guarded filter | `select_keeps_baseline_available` | PROVEN from `BaselineStaysEligible` and `MeasurementsValid` |
| Overlapping interval bounds imply every in-bound execution is faster | `not_per_execution_dominance` | DISPROVEN. This is `SoftwareIsQuantifiable.Pareto.not_per_execution_dominance` (claim 4′) |
| A gate acceptance on bounds `[10,20]` to `[8,18]` still allows a slower execution, 18 against 10 | `accepted_not_per_execution` | DISPROVEN for per-execution non-regression |
| An unchanged symbol that depends on a changed context node is in `Cone`, and the symbol is not itself a changed seed | `unchanged_symbol_context_recheck` | PROVEN |
| Ariane 5 shape: symbol `inertial` unchanged, context `trajectory` changed. The symbol-only cone does not contain `inertial`. The context edge does | `ariane_symbol_only_misses`, `ariane_context_cone_catches` | PROVEN |
| CrowdStrike 2024 shape: symbol `sensor` unchanged, data node `contentTemplate` changed. The symbol-only cone misses `sensor`. The data edge catches it | `crowdstrike_symbol_only_misses`, `crowdstrike_data_cone_catches` | PROVEN |
| Knight Capital shape: symbol `router` unchanged, `configFlag` and `rollout` changed. The symbol-only cone misses `router`. Each of those nodes puts `router` in `Cone` | `knight_symbol_only_misses`, `knight_config_cone_catches`, `knight_deployment_cone_catches` | PROVEN |
| `accepts` holds only for a strict gain that drops no qualified behavior and worsens no bound endpoint, and the step otherwise keeps the incumbent | `accepted_strict`, `step_witness`, `accepts_complete` | PROVEN for that definition |
| On a stream, shipped releases stay `noRegress` related. If the finite universe contains a strict improvement, `ascend` ships one and is undominated by that universe after `length` steps | `shipped_chain`, `ascend_ships_of_exists`, `ascend_frontier` | PROVEN |
| Keeping every release is non-regressing and still refuses a strict improvement. A boolean gate that matches a relation decides that relation | `not_every_gate_complete`, `complete_gate_decides` | DISPROVEN for "every gate is complete without a decider" |
| Qualified behavior that was never in the qualified list can disappear while `accepts` is true. If `Pareto.accepts trueBs inc`, the kept list still contains `trueBs` | `not_unobserved_nonregression`, `nonregression_if_coverage` | DISPROVEN without the coverage hypothesis. The implication is proved. Coverage itself is not proved |
| Per-symbol strict acceptance implies the summed axis bounds and tagged behavior sets of a block do not regress, and stay strict when symbol ids are unique | `finer_bounds`, `finer_behaviors`, `finer_strict` | PROVEN |
| One merged block can accept a step that the per-symbol gate refuses | `coarse_admits_symbol_regression` | DISPROVEN for "a coarse gate refuses every per-symbol regression" |

`Cone` has node kinds `symbol`, `context`, `data`, `configuration`, and `deployment`. `symbolSeeds` and `symbolDeps` drop every non-symbol. The three counterexamples are finite graphs in `ContextCone.lean`, not incident narratives and not measurements.

`./check.sh` on this tree exits 0. `gate examples/stream.json` prints:

```
r0 ship r0
r1 accept ship r1
r2 refuse emit ship r1
r3 refuse-equal ship r1
```

`Implications.lean` prints each headline as `IMPLICATION`, `FROM`, `PLUS`. Those lines are in `CHECK.log`. No separate implications prose is maintained.

Nothing here is a measurement of Ariane 5, CrowdStrike, or Knight Capital, and nothing here ranks one implementation against another.
