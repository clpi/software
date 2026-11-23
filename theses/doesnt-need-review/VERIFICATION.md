# Verification boundary

The publisher ran `sh check.sh` with Lean 4.19.0 (`6caaee842e94`, x86_64 Linux)
and Lake `5.0.0-6caaee8` (Lean 4.19.0). The complete successful output is
[`verification/publisher.log`](verification/publisher.log). The gate now checks
actual direct-PATH and package-resolved version output against both
`lean-toolchain` files, instead of relying solely on the declared pin.

## What was checked

- All **23 accepted Lean source files** in both isolated Lake packages were
  discovered, including otherwise unimported files, examples, helper scripts,
  private declarations, and generated kernel-safe declarations. All four added
  modules are also explicit Lake roots, so package dependencies are rebuilt.
- Every accepted source was compiled with warnings as errors into a fresh
  temporary `.olean`. The axiom auditor imported that exact artifact without
  changing its imports before proof elaboration.
- The source gate rejects proof admissions, explicit custom axioms,
  `native_decide`, explicit unsafe declarations, external implementations,
  implementation substitutions, and the covered diagnostic/kernel-check
  weakening forms. The elaborated declaration audit follows axiom dependencies
  and allows only Lean's standard `propext`, `Classical.choice`, and `Quot.sound`.
- All **12 gate controls** passed or were rejected as intended, including an
  unimported file, a failing theorem, a warning, and a metaprogram-generated
  custom axiom that ordinary compilation accepts but the kernel axiom audit
  rejects. Original invalid fixtures remain in-tree as `.negative` files and
  run only as explicit rejection controls.
- All **18 semantic counterexample theorems** compiled: ten retained in
  `statement/ReviewControls.lean` and eight added in
  `statement/ReviewStrengtheningControls.lean`. Their exact witnesses and scope
  are listed in [COUNTEREXAMPLES.md](statement/COUNTEREXAMPLES.md).
- Four finite-checker guards cover redundant added support, relevant changed
  support, malformed input even with an empty relevant list, and harmless
  irrelevant support with different universes. General acceptance, rejection,
  and unestablished equivalences are theorem terms, not inferred from examples.
- The imports matched exact Git commit pins, Git blob hashes, and SHA-256 values
  for all ten source files in `imports.lock.json`. Legacy revisions also
  matched; the two environments remain separate and no upstream pin changed.
- The legacy axiom/dependency gate and examples passed. The existing range-ledger
  example matched native SQLite SUM in **7,737 split/merge comparisons** and
  rejected its planted stronger false claim. That example count does not
  establish requirements completeness for another system.
- The accepted Lean source inventory and contents stayed unchanged throughout
  the all-file run. `git diff --check` was clean.

## Propositions now have proofs

The original `FullClosureClaim`, `RelevantClaim`, and `OmissionClaim` definitions
were not changed. The statement-only base was
`3552dfd7c1e63eeea15182bd827543dd44385b23`. This revision adds their proof terms:

| Proposition/result | Checked theorem | Logical axiom dependencies |
|---|---|---|
| `FullClosureClaim` | `ReviewStatement.full_closure_claim` | None |
| `RelevantClaim` | `ReviewStatement.relevant_claim` | None |
| `OmissionClaim` | `ReviewStatement.omission_claim` | None |
| More general four-premise prospective core | `ReviewStatement.prospective_omission` | None |
| Stronger nonvacuous application theorem with weaker decision invariant | `ReviewStatement.review_omission` | None |
| Old projection invariant implies decision invariant | `ReviewStatement.respects_decisions_of_respects_relevant` | None |
| Exact positive root/rule absorption characterizations | Five named variants in `ReviewProofs.lean` | None |
| Any fixed projector transports equal closures | `ReviewStatement.same_decisions_of_full_closure` | Standard `propext`, `Quot.sound` |
| Pair/uniform absence of modeled load-bearing witnesses | Two iff theorems in `ReviewOmission.lean` | Standard `propext`, `Classical.choice`, `Quot.sound` |
| Finite reference-checker correctness and uniform outcome lifting | Six theorems in `ReviewFinite.lean` | Only standard logical axioms, inherited where needed from upstream closure correctness |

There are **23 new non-control theorem declarations** across `ReviewProofs`,
`ReviewOmission`, and `ReviewFinite`. This count describes the declarations;
the table and `CLAIM.md` define what they prove. A proposition definition by
itself still does not prove that proposition. The new proof terms are what
advance the three original claims from specified to proved.

The prospective core transfers truth for all relevant post-review derivations,
without assuming that every post-review rule is sound outside the relevant
slice. Its application wrapper retains objective/outcome nonemptiness, catalogue
membership, successful baseline admission, and required-objective derivability
and truth. These facts do not discharge any application's P1–P11 by themselves.

## Independent challenge and exact-pin recheck

The counterexample reviewer did not author the main statements or proofs.
Its findings rejected the false one-direction certificate converse and tested
admission/frontier separation, harmless receipt identity, hidden qualification
changes, omitted outcome coverage, and omitted relevance. All eight new
controls are standing proofs. The source-payload hashes and review scope are in
[`verification/statement-review.json`](verification/statement-review.json).

A second agent, which did not author source or the gate, must independently
fetch the final candidate commit, compare its full tracked file paths, modes,
and blob hashes to the checkout, record actual Lean/Lake versions, and re-run
`sh check.sh` with unchanged sources at that exact candidate. The default
branch advances only after this check and the final pinned semantic review
succeed. The landing report names the checked commit and tree. The publisher
log alone is not an independent exact-pin receipt.

## Trust and reproducibility limits

This is a proof-policy gate. It trusts the pinned Lean implementation, gate
implementation, operating system, and authenticated dependency retrieval. It is
not a sandbox for arbitrary hostile metaprograms, a proof of the gate or compiler,
or a tool qualification certificate under a safety standard. Matching version
self-reports also does not authenticate a malicious replacement binary.

Lean emits unsafe implementation auxiliaries for ordinary definitions and
generated instances. The auditor reports their counts separately and audits
all kernel-safe declarations and their transitive axiom dependencies. Explicit
unsafe source is rejected. Zero custom axioms does not mean that every auxiliary
or imported theorem is free of standard Lean logical axioms.

Both repository-owned Lake configurations remain TOML so the Lean configuration
DSL's custom configuration axiom is not part of accepted source. Dependency
packages remain pinned and imported proof dependencies are audited; `.lake`
caches and external package fixture trees are not repository-owned proof files.

The legacy package requires read access to its pinned private
`software-is-composable` dependency. In this environment its original signed
commit and every blob were recovered through the authenticated GitHub API;
the reconstructed Git tree and commit hashes exactly matched the pinned
upstream objects. No dependency source or revision was substituted.

No theorem here establishes requirements/model/artifact fidelity, real execution
or outcome coverage, tool qualification, permission to omit required review,
economic improvement, or global Pareto optimality. Those remain explicit
application premises. The finite comparator certifies only its encoded-model
claim; its upstream reference algorithm enumerates subsets and carries no
scalability claim.
