# software-doesnt-have-to-regress

**Claim scope:** a release process can preserve its declared, faithfully represented qualification and cost contract by publishing a certified incumbent or a checked replacement. It may have to block. Strict improvement, uninterrupted availability, complete physical coverage, and global optimality are not consequences of this claim.

[The definition audit](AUDIT.md) gives the candidate readings, minimal counterexamples, surviving conjunction, enforcement costs, and model limits. The requested historical pin `24d36c13414867e59ae67ccf47f83cc250ce55af` was README only; this development does not retroactively credit it.

`Audit.Contract` adds separate required-capability and permitted-outcome checks to the pinned family cost and qualification vocabulary. It proves fixed-contract sequence preservation and a deployment wrapper that blocks an uncertified baseline. `Audit.Readings`, `Audit.ContractControls`, and `Audit.Projection` retain the independent counterexamples and information-erasure limits. These are finite model results. The legacy `gate` executable below still implements the original narrower profile policy; it has no outcome-envelope input or physical evidence extractor.

Lean 4.19.0, core only. `./check.sh` inventories and recompiles every repository Lean file with warnings as errors, checks both dependency pins, scans source escapes, audits every proposition-valued declaration's transitive axioms, runs standing rejection controls, and checks both worked examples and the stream executable. Fresh logs and source fingerprints are in `.lake/all-files-gate/`. `CHECK.log` is a historical transcript, not current-pin evidence. Standard Lean foundational axioms and compiler-generated nonlogical runtime internals are reported separately from custom proof axioms and authored source escapes.

Pinned inputs:

- `software-is-quantifiable` `a21c7c56fa028f32014dd795b35b14f688e8fdf1`, module `SoftwareIsQuantifiable.Pareto`. `noQualifiedBehaviorLost` reads `PriorQualification.qualified`. `Coverage.coverage` is `PlatformPremise.mediated`, a premise.
- `software-is-composable` `033c12c01299a9b28983bee410c230641adc7d1e` (`033c12c0`), `require`d from git. Admission is `SoftwareIsComposable.Admission`.

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
| Qualified behavior that was never in the prior qualified set can disappear while `accepts` is true. If `noQualifiedBehaviorLost` holds for prior set `trueBs` against the incumbent's offered behaviors, that set is still offered by the candidate | `not_unobserved_nonregression`, `nonregression_if_coverage` | DISPROVEN without the prior-qualification hypothesis. The implication is proved. Upstream `Coverage.coverage` is a premise, not a theorem |
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

`Implications.lean` retains the dependency-report helpers and headline axiom prints. The generated gate audit invokes its report and audits every logical declaration, including the definition-audit modules. The historical `IMPLICATION`, `FROM`, and `PLUS` output remains in `CHECK.log`; current evidence is generated under `.lake/all-files-gate/`. See [the claim ledger](AUDIT.md#7-proof-strength-and-application-premise-ledger) for the physical-coverage and deployment premises.

Nothing here is a measurement of Ariane 5, CrowdStrike, or Knight Capital, and nothing here ranks one implementation against another.
