# software-doesnt-need-review

**Claim:** a named review can be omitted for a pinned set of objectives only
when independent evidence already discharges those objectives, the review
cannot change their qualification or the declared admission/frontier decisions,
and the applicable assurance process permits the substitution.

The repository title is not an unconditional assertion that human review is
unnecessary. [CLAIM.md](CLAIM.md) is the authoritative statement, including its
falsifiers, imported definitions, evidence obligations, and open premises.

## Status at this change

| Claim or obligation | Status and evidence |
|---|---|
| Full qualification closure is unchanged exactly when the two normalized bases mutually preserve each other's closure | SPECIFIED, NOT PROVEN here: `ReviewStatement.FullClosureClaim` |
| Equality on a declared relevant slice preserves candidate admission and the frontier through a projection that respects that slice | SPECIFIED, NOT PROVEN here: `ReviewStatement.RelevantClaim` |
| Prospective omission preserves declared objectives for every admissible review outcome under the stated independent evidence and soundness hypotheses | SPECIFIED, NOT PROVEN here: `ReviewStatement.OmissionClaim`; application premises P1–P11 remain explicit |
| Narrow incremental recheck equivalence under its existing cost validity and unchanged-outside-cone hypotheses | Existing theorem: `Narrow.narrow_recheck_iff` |
| A review bit agrees with admission when agreement with recheck is supplied as a hypothesis | Existing conditional theorem: `Narrow.narrow_rubber`; not a proof that human judgment always factors through the checker |
| Valid roots and valid rules suffice for true derived conclusions | Imported theorem: `Qualification.soundness`; validity is not proved by derivability |
| A derivable false atom refutes the conjunction of root/rule validity | Existing theorem: `Narrow.sound_needs_premises` |
| Passing a checker alone makes review unnecessary | REFUTED by the existing specification-boundary controls and the new [standing controls](statement/COUNTEREXAMPLES.md) |
| Concrete regulated deployment may omit review, or omission saves resources | OPEN APPLICATION PREMISES; no such deployment or economic result is certified here |

The initial audit pin `ae5f3918f7689267d07044a00e6a11b071510bba` contained only
the README. The inspected starting head for this change was
`1d504014be0c727b3f12e4d8e17f47dfceb118b6`, which already contained the narrow
lemmas and examples. This change preserves them and supplies the explicit
family-level statement requested by the audit follow-up.

## Reproduce

Use Lean `leanprover/lean4:v4.19.0` and run `./check.sh` with `lake` on `PATH`.
The repository gate checks every accepted `.lean` file, the legacy package,
the isolated statement package, proof axiom dependencies, and standing controls.
Intentionally invalid source fixtures use `.negative`, never the accepted-source
extension. See [VERIFICATION.md](VERIFICATION.md) for the exact check record and
trust limits.

The new statement imports `software-optimality` at
`0bbc1f3b8aa38afe17e02ccbd7ddd0e7722b3cb0` and `software-is-quantifiable` at
`d88acbdc3ba78fff994067d2c73bcc01622b3f61`. [imports.lock.json](imports.lock.json)
records the imported declarations. Its separate Lake package avoids mixing
the legacy composable package's vendored module names with the current
optimality definitions. A successful build of a proposition definition is
**statement typechecking, not a proof of that proposition**.
