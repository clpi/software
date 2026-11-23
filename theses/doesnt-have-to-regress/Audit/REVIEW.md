# Independent challenge and proof-strength review

## Scope

The review covers the new definition audit and finite contract added above historical request pin `24d36c13414867e59ae67ccf47f83cc250ce55af` and live baseline `858a85e383fbecc9826186aee2cc0101aea5ea62`.

The contract/projection author, counterexample author, source-provenance reviewer, and check-gate author were separate agents. The counterexample author challenged the contract independently; the source-provenance reviewer challenged the gate independently. Source review is not a substitute for an exact-commit build.

## Contract challenge

No false theorem was found in the reviewed `Audit.Contract` or `Audit.Projection` development.

The independent controls remove capability retention, allowed-outcome protection, cost comparison and context equality separately. Each omission has a concrete finite failure. Additional controls exercise optional feature changes, qualification accumulation, identity relocation, empty scope, missing capability/execution linkage and invalid-baseline handling.

### Resolved findings

| Attack | Resolution |
|---|---|
| Required capability remains, but a forbidden outcome appears | Capability and outcome types are distinct; the permitted-outcome check independently rejects the new outcome. |
| An optional new feature disappears after being promised | `recordPromises` appends qualification; the release must be certified against the expanded contract before it becomes the next baseline. |
| Capability is moved from one API/key to another | The required old key is still checked; the moved capability does not discharge it. |
| A refused candidate causes the helper to keep an invalid incumbent | The public `deploy` wrapper returns `none` when the incumbent is uncertified; `deployed_safe` has the successful-return premise instead of an unchecked eligibility premise. |
| Equal observations hide order, a deadline, or environment | The exact-checker impossibility theorem is explicit; conservative refusal remains possible. No claim is made that the entire family or Lean cannot encode richer observations. |
| Cost-only or scalar-score improvement deletes functionality or trades a protected coordinate | Standing reading controls reject both inferences. |

### Remaining application premises

These are not kernel-checked claims about the implementation:

1. **Capability fidelity:** an offered capability is actually provided with its intended quantifiers.
2. **Outcome coverage:** every relevant possible implementation outcome is represented.
3. **Execution linkage:** capability, outcome and cost projections describe the same coherent implementation.
4. **Scope coverage:** declared protected keys cover the entire claimed API/workload/environment scope.
5. **Context authenticity:** equal context values denote genuinely comparable physical and measurement conditions.
6. **Cost fidelity:** the represented minimizing natural-number coordinates correctly encode the claimed costs. The theorem uses two coordinates per protected key.
7. **Composition fidelity:** local costs imply the desired integrated-system costs through a justified law, or integrated costs are directly protected.
8. **Qualification governance:** new promises are recorded and prior promises are not silently dropped.
9. **Deployment correspondence:** the published artifact is the artifact represented by the checked result.
10. **Temporal and probabilistic interpretation:** timing, liveness, ordering, risk and environmental claims have the richer semantics and evidence their statements require.

An empty key inventory protects nothing. A declared capability with an empty possible-outcome list is accepted by the abstract checker because operational linkage is not part of that record. Both are retained counterexamples to an unqualified physical reading, not counterexamples to the scoped theorem.

## Independent gate challenge

The reviewer found two real defects in the first gate draft:

- A double-quote character literal confused string stripping and could conceal an authored unsafe declaration.
- Custom elaboration could synthesize an unsafe declaration that a source-only scan did not see.

The retained refusal controls are `controls/QuotedEscape.lean.fail`, `controls/GeneratedEscape.lean.fail`, and `controls/SpoofedRuntime.lean.fail`. They are deliberately invalid-for-the-gate fixtures, not admitted Lean proof sources. The checker lexes character/raw/string/comment forms, restricts authored metaprogramming, and checks compiled declarations' safety and source provenance. Compiler-generated nonlogical internals are separately reported.

The stream parser was also tightened to reject ambiguous duplicate keys, trailing commas, leading-zero natural numbers, and raw control characters. This is a restricted reader for the existing stream schema. The mathematical release contract does not depend on an unstated claim that this reader implements every JSON feature.

## Frozen mathematical sources reviewed

| File | SHA-256 |
|---|---|
| Audit/Contract.lean | 8068ca383cd9107eb88b08d6525cb4d353f1cfcfc42f49f262510dbea205d09e |
| Audit/ContractControls.lean | bb54e4c579eb1647e18e6bd93cfec01f4457fc9be039626101560c22f17a3e79 |
| Audit/Projection.lean | 333037a0dd3ee5759301e787b7e0dbf46832c8535866b87b8ad97623d2340a10 |
| Audit/Readings.lean | 8be778e4221dbb3f0d5f3e007c7ee7026eb20136089e8908b5b464ef5f96faad |

The independent module checks used Lean 4.19.0 with `-DwarningAsError=true` and exited 0 without diagnostics. The final gate must also pass after all gate/configuration changes.

## Exact-pin closure protocol

1. Freeze all Lean sources, checker inputs and dependency revisions.
2. Run `./check.sh`; reject any source/configuration change during the run.
3. Create the candidate commit without changing the checked sources.
4. Independently retrieve its tree and file contents from the remote commit, verify Git blob hashes and modes, and verify the two dependency source trees at their pins.
5. Rebuild from clean outputs and rerun the same complete gate.
6. Move the default branch to that exact verified candidate using an expected-head check. If the default head changed, inspect and revalidate the integration.

Fresh receipts under `.lake/all-files-gate/` identify every compiled source and checker input. Historical `CHECK.log` and interrupted or source-changing runs do not count as current-pin evidence. The proof claims remain limited to the exact verified source and the explicit premises above.
