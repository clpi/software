# software-doesnt-need-review

Lean 4.19.0, core only. `./check.sh` builds with warnings as errors, refuses `sorry`, `admit`, and custom axioms, prints `#print axioms`, and checks the import listing from `scripts/UpstreamDeps.lean`. That listing is not copied here.

`software-is-composable` is required at `033c12c01299a9b28983bee410c230641adc7d1e`.

## Claims

| Claim | Status |
|---|---|
| For a change inside a sound cone (`ClosureHyp`, discharged by `inClosure_iff_affected`) whose spec, roots, and rules are unchanged, rechecking the machine-checked property is equivalent to re-reviewing that property (`narrow_recheck_iff`). The review bit is then the certifier's bit (`narrow_rubber`) | PROVEN |
| The cone hypothesis holds for the context-aware call closure (`closureHyp_of_affected`) | PROVEN |
| A derivation is true only when `validRoots` and `validRules` hold (`sound_needs_premises`, from `Qualification.soundness`) | PROVEN |
| Review is redundant given certification, including when the spec is wrong | DISPROVEN |
| Opaque unit tokens: the allow-list accepts and the units differ (`mco_boundary`, `mco_rule_invalid`) | DISPROVEN |
| One AOA sensor: the single-sensor rule accepts and two sensors are required (`mcas_boundary`, `mcas_not_two`, `mcas_rule_invalid`) | DISPROVEN |

The elimination argument is the narrow theorem. The mechanism is in PROPOSAL.md.
