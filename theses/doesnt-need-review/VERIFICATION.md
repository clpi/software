# Verification boundary

The publisher ran `sh check.sh` successfully with Lean 4.19.0
(`6caaee842e94`, x86_64 Linux). The complete output is
[`verification/publisher.log`](verification/publisher.log).

## What was checked

- All **19 accepted Lean source files** in both isolated Lake packages were
  discovered, including otherwise unimported files, examples, helper scripts,
  private declarations, and generated kernel-safe declarations.
- Every accepted source was compiled with warnings as errors into a fresh
  temporary `.olean`. The axiom auditor imported that exact artifact; it did not
  change the source's imports before proof elaboration.
- The source gate rejects proof admissions, explicit custom axioms,
  `native_decide`, explicit unsafe declarations, external implementations,
  implementation substitutions, and the covered diagnostic/kernel-check
  weakening forms. The elaborated declaration audit follows axiom dependencies
  and allows only Lean's standard `propext`, `Classical.choice`, and `Quot.sound`.
- All **12 gate controls** passed or were rejected as intended, including an
  unimported file, a failing theorem, a warning, and a metaprogram-generated
  custom axiom that ordinary compilation accepts but the kernel axiom audit
  rejects. Original planted invalid fixtures remain in-tree with the
  `.negative` extension and are run only as explicit rejection controls.
- All **10 semantic counterexample theorems** in `statement/ReviewControls.lean`
  compiled. Their precise scope is listed in
  [`statement/COUNTEREXAMPLES.md`](statement/COUNTEREXAMPLES.md).
- The statement's definition imports matched the exact Git commit pins,
  Git blob hashes, and SHA-256 values in `imports.lock.json`. Legacy dependency
  revisions also matched; the two environments are not mixed.
- The existing legacy axiom/dependency gate and examples passed. The existing
  range-ledger example matched native SQLite SUM in **7,737 split/merge
  comparisons**, and rejected its planted stronger false claim. This example
  count is not evidence of requirements completeness for any other system.
- The Lean source inventory and contents stayed unchanged throughout the
  all-file run. `git diff --check` was clean.

## Statement versus proof

`FullClosureClaim`, `RelevantClaim`, and `OmissionClaim` are complete Lean
propositions, not theorem terms. A successful build proves that their
declarations are well typed. It does **not** prove those propositions or
instantiate any application's P1–P11 obligations. No main-claim proof body,
proof admission, or custom axiom is supplied.

The new controls are actual proofs of counterexamples to stronger, invalid
claims. The earlier narrow incremental theorems remain conditional on their
original hypotheses; in particular, `narrow_rubber` assumes agreement of the
review bit and the recheck.

## Independent challenge and pin discipline

An agent separate from the statement author attempted counterexamples to the
algebraic and application claims. Its material findings were incorporated:
prospective outcome coverage, preservation of fresh provenance, normalized
withdrawals, two-direction closure certificates, nonvacuous successful
admission, fixed epochs, and explicit artifact-authentication assumptions.
The reviewed payload hashes and remaining proof obligations are recorded in
[`verification/statement-review.json`](verification/statement-review.json).

The default branch may advance to a candidate only after another agent re-runs
the complete gate against the exact candidate commit's source tree and confirms
that the tree is unchanged. The final landing report must name that commit.
The preceding publisher log alone is not an independent post-commit receipt.

## Trust and reproducibility limits

This is a proof-policy gate. It trusts the pinned Lean implementation, gate
implementation, operating system, and authenticated dependency retrieval. It
is not a sandbox for arbitrary hostile metaprograms, a proof of the gate or
compiler implementation, or a tool qualification certificate under a safety
standard.

Lean emits unsafe implementation auxiliaries for ordinary definitions and
generated instances. The auditor reports their counts separately and audits
all kernel-safe declarations and their transitive axiom dependencies. Explicit
unsafe source is rejected. Standard logical axioms are distinguished from
custom axioms; “zero custom axioms” does not mean “no standard Lean axioms.”

Lake's Lean configuration DSL generates a custom configuration axiom. Both
repository-owned configurations were translated with Lake 4.19's own
`translate-config` into equivalent TOML, preserving pins, options, version,
roots, and targets, so no configuration exception is needed for accepted Lean
source. Dependency packages remain pinned and their imported proof dependencies
are audited; `.lake` caches and external package fixture trees are not counted
as repository-owned proof files.

Running the legacy package requires read access to its pinned private
`software-is-composable` dependency. In this environment its original signed
commit and every blob were recovered through the authenticated GitHub API;
the reconstructed Git tree and commit hashes exactly matched the pinned
upstream objects. No dependency source or revision was substituted.

No formal result here establishes model fidelity, real execution coverage,
tool qualification, permission to omit review, economic improvement, or global
Pareto optimality. Those remain the expressly scoped premises and future proof
obligations in `CLAIM.md`.
