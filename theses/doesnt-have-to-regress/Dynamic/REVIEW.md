# Independent challenge record

This extension starts from source pin
`f07f8e7595eb70afe84a40403f54481dfc22f6cc`. The incremental evaluator,
greedy selector, reversible-history implementation and integration were
developed separately. The incremental author independently attacked the
greedy/evolution/integration modules and wrote the executable controls. The
greedy author independently attacked incremental reuse and history, reviewed
the strengthened integration wrappers, and prepares the clean remote-pin
recheck. Authors' own successful checks are not independent closure.

## Findings and resolutions

| Attempt | Finding or resolution |
|---|---|
| Reuse a success after changing required capabilities, outcome envelope, possible outcomes, cost, protected key or context | Every evaluator dependency appears in its exact stamp. Standing controls force new leaf evaluations and the correct changed verdict. |
| Cache a false verdict and turn it into acceptance | Each entry carries `verdict = evaluate stamp`; positive and negative proof reflection are both kernel-checked. |
| Call the cached checker with a complete but weaker contract and infer authority to erase old promises | Exactness of that query does not authorize evolution. `Evolution.strengthens` and `Engine.adopt` reject erasure. |
| Demand that an old release satisfy a new feature promise before the feature can be introduced | The admitting release is checked under the old contract and then the new contract. An independent two-phase-adoption control passes while the old release fails the new promise. |
| Add a protected key and claim it was historically cost-protected | Refuted. The new key establishes its baseline on admission; subsequent worsening is refused. |
| Reuse an invalid incumbent as fallback | Raw helper counterexample retained. Public cached `select` and `deploy` block invalid baselines, including empty search lists, and prove safety from successful return. |
| Keep only new arrivals after scope changes | A previously tied archived candidate becomes strictly better on the newly protected key. Accepted contract changes automatically rescan the complete archive. |
| Treat missing archived key observations as the projection's zero-cost default | A real adapter defect was found independently. Scope expansion now requires all archived profiles to contain the new keys; reconsideration, rollback and undo defensively check current coverage. The failing shape is a permanent JSON control. |
| Store a failed contract proposal's improving candidate but never select it under the still-active contract | A real greedy invariant gap was found. Refused contract proposals also rescan the retained archive under the unchanged contract; the new promise remains refused. |
| Infer global optimality from greedy maximality | Refuted by an omitted better candidate and by incomparable order dependence. The theorem quantifies only over the supplied catalogue. |
| Infer greedy individual edits find beneficial interactions | Refuted by two individually harmful edits whose combination improves. Bounded fixed-order include/exclude enumeration recovers the interaction; its exponential size and permutation limits are explicit. |
| Infer no intervening writes from checked inverse before-values | Refuted by an ABA sequence. The value-freshness boundary is explicit and theorem-checked; `undoRecorded` additionally requires a known source event. |
| Undo a strict optimization or erase a promised feature | Structural inverse and current-contract publication are separate. The current admission check refuses the regressing inverse. |
| Change epoch by replacing the incumbent or omitting inconvenient archived artifacts | The executable requires the same incumbent identity, complete reobservations of all archived identities, unchanged obligations and explicit new contexts. No cross-context physical dominance is claimed. |

The mathematical proofs establish finite represented facts. The independent
controls also retain the limits of linear cache lookup, erased runtime proof
fields, pure-state reversal, submitted observation fidelity and finite search
coverage. See [DYNAMIC.md](../DYNAMIC.md) for exact claim/premise mappings.

## Closure procedure

Freeze the source and gate inputs, run the complete root gate, publish a
candidate commit, independently fetch and hash its exact remote tree and
blobs, rebuild from source-only dependencies at their immutable pins, and
rerun the complete gate. The default branch must receive that same verified
commit. Store receipts and logs in an evidence-only descendant so adding
evidence cannot silently change the verified source pin.

This review record is a source-challenge report, not a self-certifying claim
that those later exact-pin steps passed. The generated receipts and the
separate verification record identify the actual checked commit, hashes,
compiler version, complete file inventory, proof audit and runtime controls.
