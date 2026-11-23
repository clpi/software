# software-doesnt-need-review

**Proved claim:** for a fixed contract, catalogue, and relevant objective slice,
valid independent baseline evidence, uniformly conservative review outcomes,
and a decision projection that respects that slice preserve qualification,
admission, and the frontier. A successful application
also retains the named subject's admission and proves every required objective
both derivable and true before and after every allowed review outcome.

The repository title does not assert that all human review is unnecessary.
[CLAIM.md](CLAIM.md) is the authoritative formal claim, including exact imports,
falsifiers, discharging evidence, and open application premises. Permission to
omit a mandated activity remains external to the mathematical result.

## What improved at this change

| Claim or obligation | Status and evidence |
|---|---|
| Exact full-closure equality iff mutual root/rule absorption | **PROVEN**: `ReviewStatement.full_closure_claim : FullClosureClaim` and `basis_conservative_iff` |
| Relevant qualification equality preserves decisions through the original projection invariant | **PROVEN**: `ReviewStatement.relevant_claim : RelevantClaim` |
| Original prospective omission proposition | **PROVEN**: `ReviewStatement.omission_claim : OmissionClaim`; original proposition unchanged |
| Weaker decision-level invariant suffices, while required post-review derivability and truth are retained | **PROVEN**: `ReviewStatement.review_omission`; more general four-premise core `prospective_omission` |
| Decision noninterference is strictly weaker than equality of the complete projected inputs | **PROVEN** implication plus nonvacuous separating counterexample in `ReviewStrengtheningControls` |
| Exact root-only, rule-only, combined positive-addition, and uniform-outcome absorption conditions | **PROVEN** in [ReviewProofs.lean](statement/ReviewProofs.lean) |
| Technical redundancy iff there is no changed relevant atom, subject admission, or frontier | **PROVEN** pair and uniform-outcome characterizations in [ReviewOmission.lean](statement/ReviewOmission.lean) |
| Finite checker acceptance, disagreement, and malformed-input cases, plus complete-outcome lifting | **PROVEN** in [ReviewFinite.lean](statement/ReviewFinite.lean); composes the pinned upstream closure checker |
| Narrow incremental recheck equivalence | Retained existing conditional theorem: `Narrow.narrow_recheck_iff` |
| A review bit agrees with admission given agreement with recheck | Retained `Narrow.narrow_rubber`; its review-bit hypothesis is still explicit |
| Passing a checker alone establishes requirements fidelity or permission to omit review | **REFUTED** by the specification-boundary and [18 standing counterexample theorems](statement/COUNTEREXAMPLES.md) |
| A production deployment may omit review, or omission saves resources | **OPEN APPLICATION PREMISES** P1–P11; no such deployment or economic result is certified |

The three original F1–F3 proof terms and the stronger prospective core/application
theorems are axiom-free. Some supporting extensionality, classical equivalence,
and imported finite-checker correctness proofs use Lean's standard logical
axioms; the repository gate allows no custom axioms or unfinished proofs.

## Exact authority and history

The initial audit pin `ae5f3918f7689267d07044a00e6a11b071510bba` was README-only.
The initial statement landed at `3552dfd7c1e63eeea15182bd827543dd44385b23`, after
the earlier narrow lemmas. This improvement proves the same original
propositions and extends them; earlier pins retain their original claim status.

The statement package still imports `software-optimality` at
`0bbc1f3b8aa38afe17e02ccbd7ddd0e7722b3cb0` and `software-is-quantifiable` at
`d88acbdc3ba78fff994067d2c73bcc01622b3f61`. [imports.lock.json](imports.lock.json)
records the exact declaration/file mapping and content hashes. No upstream pin
changed. Its separate Lake package prevents the legacy composable package's
vendored module names from replacing the current optimality definitions.

## Reproduce

Use Lean `leanprover/lean4:v4.19.0` and run `./check.sh` with `lake` on `PATH`.
The gate verifies the running Lean/Lake versions against both toolchain files,
builds all declared modules, and discovers and checks every accepted `.lean`
file, including unimported examples and helper scripts. It enforces warnings as
errors, escape scans, and a transitive kernel-axiom audit.

[VERIFICATION.md](VERIFICATION.md) records the checks and trust boundary.
Intentionally invalid source fixtures use `.negative` and run as explicit
rejection controls. No successful build or proof-policy gate establishes
real-world scope completeness, model fidelity, or safety-tool qualification.
