# Return proof repair: a two-voice review

## Result and evidence boundary

The unrestricted strengthening is **false**. A witnessed head does not imply any derivation under the original arbitrary lifting. The old `returns_head` has been removed, including its conclusion-equivalent `contributed` premise and unused `_witnessed` premise. There is no compatibility theorem that preserves the circular statement under another name.

This revision provides an unconditional theorem relating an executable contributor search to the fold, an explicitly **weaker** recorded-edge source-recovery theorem, and a separate head-recovery theorem for a concrete restricted recording construction. The latter uses its witnessed-head hypothesis. Ten standing counterexamples constrain the interpretation of these results.

The mathematical claims in this report attach to the sources in this revision, with their exact inputs recorded in [SOURCE-SHA256.txt](SOURCE-SHA256.txt) and [CHECK.log](CHECK.log). The changed-source count is **56 explicit named theorems in five Lean files**, compared with 43 in four files at the baseline. The gate also audits generated/private theorem declarations; those are not counted as additional authored theorems.

## Voice One — Reproduce the audited pin and its dependencies

The starting point is `clpi/software-is-more-traceable-than-you-think` at **`8f6a128069d0e68e97c4a69d78689c84350b0d2f`**. The corresponding [family census](https://github.com/clpi/software-is-a-closed-loop/blob/ae85d7aa2d17/census/software-is-more-traceable-than-you-think.md) was read at `software-is-a-closed-loop@ae85d7aa2d17`. The source repository's default branch still identified the stated starting pin when this repair began.

All four original Lean files, all three gate scripts, the toolchain pin, and the proof documentation were read. Fetched source bytes were checked against the Git blob identities at the starting commit. The exact proof/gate input identities are in [baseline-inputs.txt](receipts/baseline-inputs.txt). The two large JSON data artifacts are outside the Lean dependency graph and were not replayed or changed in this repair.

The baseline was independently executed with Lean 4.19.0:

- `sh proof/check.sh`: exit 0, [complete original-gate output](receipts/baseline-proof.log).
- `sh examples/check.sh`: exit 0, including its nested range-ledger gate and the rejected wrong-bridge mutation; [complete output](receipts/baseline-examples.log).
- An additional baseline enumeration printed dependencies for **all 43 named theorems**, including the five construction theorems the original proof gate did not print. All dependencies stayed within `{propext, Quot.sound}`; [complete output](receipts/baseline-axioms.log).

The original statement and proof were:

```lean
theorem returns_head (lift : Ev → Graph Node)
    (_witnessed : (fold lift l).nodes d.head = true)
    (contributed : ∃ e, e ∈ l ∧ (lift e).edges d = true) :
    (fold lift l).edges d = true :=
  (fold_edges lift).mpr contributed
```

`fold_edges` already equates `contributed` with the conclusion. The proof term does not use `_witnessed`. Its logical dependency is `fold_edges`, whose induction follows `fold`, `join`, and `empty`. No other Lean theorem calls `returns_head`. Its direct in-tree references were its own axiom/statement print commands and the old proof report; all have been updated. The other uses of `fold_edges`, including the grain controls and retraction proof, remain valid and are rechecked.

The original `Graph` has two independent fields: `nodes : Node → Bool` and `edges : Derivation Node → Bool`. Nothing in `Graph`, `lift`, or `fold` couples them. That missing relationship is the reason the name cannot be justified by deleting a premise.

## Voice One — The replacement proof

### General model: executable extraction, explicitly weaker than head-only recovery

For the original arbitrary lifting, define:

```lean
def contributor (lift : Ev → Graph Node) (l : List Ev)
    (d : Derivation Node) : Option Ev :=
  l.find? (fun e => (lift e).edges d)
```

The principal theorem has **no propositional hypotheses**:

```lean
theorem contributor_isSome (lift : Ev → Graph Node)
    (l : List Ev) (d : Derivation Node) :
    (contributor lift l d).isSome = (fold lift l).edges d
```

The recursive union fold and the first-success stream search agree for every supplied lifting, stream, and full derivation. This is not a premise saying that a contributor exists. It is an equality about two defined computations, proved for all inputs.

A successful search also carries independently proved soundness:

```lean
theorem contributor_sound (lift : Ev → Graph Node)
    (found : contributor lift l d = some e) :
    e ∈ l ∧ (lift e).edges d = true
```

The former theorem is replaced by the accurately named result:

```lean
theorem returns_recorded_edge_weaker (lift : Ev → Graph Node)
    (recorded : (fold lift l).edges d = true) :
    ∃ e, contributor lift l d = some e ∧
      e ∈ l ∧ (lift e).edges d = true
```

Here the contributor is **derived**, as a successful result of the implemented search. `contributor_isSome` turns folded edge presence into search success; the `Option` result supplies the event; `contributor_sound` establishes membership and exact contribution. There is no contributed-edge premise and no witnessed-head premise.

This is a computational refinement of edge losslessness, not a new claim that all heads have derivations. It needs the retained stream and a complete queried derivation. No equality decision on nodes, events, or derivations is needed for this generic search: its Boolean edge predicate is supplied by the lifting.

### Restricted representation: genuinely use a witnessed head

Define a recorder that constructs both faces from the same stored derivation:

```lean
def recordLift [DecidableEq Node] [DecidableEq (Derivation Node)]
    (record : Ev → Derivation Node) (e : Ev) : Graph Node :=
  ⟨fun n => decide ((record e).head = n),
   fun d => decide (record e = d)⟩
```

There is no abstract field asserting global head completeness. The relationship comes from this concrete data construction. The theorem is:

```lean
theorem returns_recorded_head
    [DecidableEq Node] [DecidableEq (Derivation Node)]
    (record : Ev → Derivation Node)
    (witnessed : (fold (recordLift record) l).nodes n = true) :
    ∃ e, e ∈ l ∧ (record e).head = n ∧
      (fold (recordLift record) l).edges (record e) = true
```

Its proof explicitly consumes the witnessed-head hypothesis:

```lean
  obtain ⟨e, member, head⟩ := (fold_nodes (recordLift record)).mp witnessed
  refine ⟨e, member, ?_, ?_⟩
  · simpa [recordLift] using head
  · exact (fold_edges (recordLift record)).mpr
      ⟨e, member, by simp [recordLift]⟩
```

The head observation identifies some event in the stream. The recorder's definition establishes that event's exact edge; the fold preserves it. The conclusion returns the event's actual recorded derivation, not an arbitrary derivation selected by the caller solely because it has the same head.

This is a theorem for a **restricted recording representation**, not an unconditional strengthening for arbitrary `lift`. Equality of `Derivation Node` includes equality of the whole premise function `Node → Bool`; decidable node equality alone does not provide that capability. The Boolean-node instance in `ReturnControls.lean` supplies it constructively by comparing both premise-function outputs and the head.

## Voice Two — Attack the strengthened form

### A1. Delete `contributed`: a head with no derivation

Take one event `()` with Boolean nodes. Its lifting records head `false` and no edges. The singleton fold satisfies `nodes false = true`, while every queried derivation has edge value `false`. `head_without_derivation` checks the concrete result and `head_only_claim_fails` proves the universally quantified proposed strengthening false.

This defeats the actual unrestricted statement, not a weakened variant of its model.

### A2. Was the removed witnessed-head condition doing hidden work?

Reverse the faces: one event records edges and no nodes. `derivation_without_head` checks that an edge is present while its head node is absent. `edge_implies_head_claim_fails` refutes any generic edge-to-head implication. The independent faces must remain independent in the generic replacement.

### A3. A known head and one derivation still do not authorize another premise set

`witnessed_head_does_not_select_premises` records head `false` and a derivation requiring premise `false`. The empty-premise derivation has the same head and is absent. Head identity cannot replace exact derivation identity.

### A4. The restricted recorder does not make a head's premises unique

`same_head_distinct_recorded_premises` uses the actual `recordLift`, not a substitute. On `[false, true]`, one event records empty premises and the other records premise `false`; both derivations share head `false`, and both exact edges are present. The finite equality procedure is constructive. Any unique-premise or canonical-causal-history interpretation fails even inside the restricted representation.

### A5. Can the extractor hallucinate a contribution from the head?

`contributor_refuses_missing_edge` runs the actual new `contributor` on A1's singleton stream. It returns `none` despite the witnessed head. A theorem that promised a contributor from this head would conflict with the implementation.

### A6. Graph order independence does not mean selected-source order independence

`contributor_selection_is_order_sensitive` uses a lifting that aliases event `false` and event `true` to the same graph. The folds of `[false, true]` and `[true, false]` are equal, but the actual search returns `some false` and `some true`, respectively. Search success can be invariant while the first selected identity changes.

### A7. The graph alone cannot recover contributing source identity

The same aliased lifting gives identical folded graphs for singleton streams `[false]` and `[true]`, with the queried edge present in both. `source_from_fold_claim_fails` proves that no decoder from the graph to the original Boolean event can work for all such streams. Retaining the stream is a real input requirement.

### A8. Time independence has erased time

`time_from_fold_claim_fails` compares singleton timed streams at times 0 and 1. Their graphs are identical. No graph-only time decoder can recover both answers. An exact-time narrative cannot be inferred from time independence.

### A9. Is the new weaker theorem only the same circular premise with a different name?

The `recorded` hypothesis still describes edge presence, and edge presence is logically equivalent to contribution existence through `fold_edges`. A corollary going in the other direction is not an independent breakthrough in semantic traceability. Similarly, `recordLift` makes complete local recording true by construction; it does not prove that an existing arbitrary instrumenter has that representation.

### A10. Are the restricted equality and recorded premises themselves justified?

An equality instance for nodes is insufficient to decide equality of arbitrary premise functions. Even a correct equality procedure says nothing about whether those premises are true, sufficient, necessary, satisfied elsewhere in the graph, or faithful to an execution. Neither the source-level Python data builders nor real executions appear in these Lean theorem types.

## Voice One — Answer every attack

| Attack | Answer and disposition |
|---|---|
| A1 | **Conceded, resolved by removing the false claim.** The direct head-only strengthening fails. `returns_head` is deleted; `returns_recorded_edge_weaker` is explicitly weaker. `returns_recorded_head` applies only to the concrete coupled recorder. |
| A2 | **Resolved in the proof and controls.** The generic replacement never inspects nodes. Its source witness comes from edge/search agreement. The old witnessed-head premise was unnecessary; no converse node-face property is inferred. The restricted theorem separately uses its witnessed-head premise to obtain stream membership. |
| A3 | **Resolved by exact query/quantification.** Generic extraction takes a full derivation. Restricted recovery returns an existing event's full record existentially. Neither accepts the caller's arbitrary premise set from head equality alone. |
| A4 | **Excluded claim, formally refuted.** The restricted theorem is an existence theorem. Unique premise selection is not claimed and cannot be proved for the present representation. A future uniqueness or causal-selection policy would require new data or constraints. |
| A5 | **Resolved by the executable theorem.** `contributor_isSome` is unconditional and excludes both missed recorded edges and invented sources. The concrete missing-edge example returns `none` as required. |
| A6 | **Excluded claim, formally refuted.** The selected first event follows retained stream order. Fold equality and existence of some source remain invariant. No canonical-source claim accompanies `find?`. |
| A7 | **Excluded claim, formally refuted.** The extractor's signature includes the retained stream; the report and README now say so. A graph-only event-identity decoder would need identity-preserving additions to the representation. |
| A8 | **Excluded claim, formally refuted.** Timestamps are not recoverable from this fold. Keep timestamped witnesses separately if that information is needed. Nothing in the patch upgrades the historical batch/step-index snapshot to clock-time evidence. |
| A9 | **Conceded as a strength limit, resolved by honest attribution.** The generic advance is a verified executable search interface and its unconditional fold agreement, a computational refinement of `fold_edges`. The weaker corollary is not counted as an independent semantic traceability theorem. The restricted head theorem's guarantee comes from the new concrete recorder, not from a theorem about arbitrary instrumentation. No conclusion-equivalent existential contribution is taken as a hypothesis of either principal result. |
| A10 | **Explicit assumptions plus named open risks.** Restricted full-derivation equality is an explicit input, with a constructive finite instance, not a supplied general solver. Real-recording fidelity and semantic validity remain R1/R2; the data-pipeline bridge remains R3 below. |

No standing counterexample to the actual unconditional search equality or restricted-head theorem was found. Their proof terms check in Lean. The failed stronger forms remain as controls, rather than being left as implied promises in the prose.

## Voice One — Exactly what this revision proves

1. **Generic fold losslessness:** node/edge presence is exactly event contribution, independently on each face; complete derivation records retain their recorded premise functions.
2. **Executable search agreement:** for every lifting, stream, and complete derivation, contributor search succeeds exactly when the fold contains that derivation.
3. **Executable search soundness and the named weaker recovery:** a recorded edge yields a returned source event in the retained stream that contributes the exact queried derivation.
4. **Restricted head recovery:** for `recordLift` and the supplied equality decisions, a witnessed head has some actual recorded derivation whose edge is in the fold. The hypothesis is used.
5. **Existing generic algebra:** the graph depends only on event membership, ignores multiplicity, splits over appended streams, and retracts exactly when the stream is filtered. The timed fold also ignores its separate `Timed.time` component; an underlying event and its lifting may themselves preserve time data. These results continue to quantify over arbitrary supplied event/node/time types and liftings.
6. **Standing failures of stronger interpretations:** the ten new controls above, together with all twelve existing controls, compile and remain in the gate.
7. **Existing worked examples:** the five invoice and six bridge-repair theorem statements remain unchanged, and the wrong-middle-bridge mutation is rejected by the executable examples gate.

### Proof-strength delta

| Declaration | Conclusion and genuine input | Printed axiom dependencies |
|---|---|---|
| Removed `returns_head` | Old output-equivalent contribution premise plus unused head premise; no retained alias | Baseline `{propext}` |
| `contributor_isSome` | Unconditional search-success/fold-edge equality | `{propext, Quot.sound}` |
| `contributor_sound` | Successful actual search result implies source membership and exact contribution | `{propext}` |
| `returns_recorded_edge_weaker` | Observed folded edge implies a concrete successful search result and contributing event | `{propext, Quot.sound}` |
| `returns_recorded_head` | Witnessed head under the concrete recorder implies an event's exact recorded derivation is present | `{propext}` |
| Ten new `ReturnControls` theorems | Concrete counterexamples to the overextensions, with no assumed counterexample conclusions | Nine axiom-free; `same_head_distinct_recorded_premises` uses `{Quot.sound}` |

Source totals: `Traceability.lean` 23; `Controls.lean` 12; `ReturnControls.lean` 10; `InvoiceTrace.lean` 5; `BridgeRepair.lean` 6. Total 56. No new custom axiom, admitted theorem, or proof escape is introduced. The finite derivation-equality definition itself uses only `Quot.sound`.

## Voice One — Cannot-say list and named open risks

**Refuted within the present model, not merely awaiting a proof:** a bare witnessed head always has an edge under arbitrary lifting; an edge always has a node-face head; head identity selects a unique exact premise set; the first chosen contributor is permutation independent; source identities or timestamps can universally be reconstructed from the folded graph alone. A1–A8 identify the appropriate standing controls.

**R1 — Execution/recording fidelity, open.** No theorem establishes that every real execution emits a witness, that witnesses are authenticated, or that the lifting records every relevant event. Universal quantification over `lift` proves accounting properties given a lifting; it does not validate the instrumenter.

**R2 — Semantic and causal validity, open.** A stored derivation is a head and a Boolean premise function. It is not a proof that those premises were true, necessary, sufficient, satisfied, causally complete, or related by a valid domain rule. The recorder generates the head and edge, not nodes for all prerequisites. No transitive premise closure or least-cause theorem is added.

**R3 — Data-pipeline correspondence, open.** The Python hypergraph construction, grain extraction, and frozen witness snapshot are not imported by these Lean modules. Their previous execution receipts remain distinct empirical evidence. This repair neither reruns that pipeline nor proves correspondence between its JSON artifacts and the abstract lifting.

**R4 — Effective equality at general grain, conditional boundary.** `recordLift` needs decidable equality of full derivations. The Boolean-domain construction demonstrates one inhabited case. It does not provide equality of arbitrary functions over arbitrary, potentially infinite node types. A scalable finite record encoding and its equivalence to this model would be additional work.

**Operational scope:** the general contributor is a scan of the retained stream using the supplied edge test. No runtime benchmark, asymptotic improvement over scanning, storage saving, canonical source choice, or executable enumeration of all derivations from the graph is proved here. The theorem is query-relative; the graph's edge face is a characteristic function, not an enumerable edge table.

## Voice One — Gate repair and fresh receipts

The baseline gate scanned only `proof/`, permitted `Classical.choice`, and depended on manually supplied axiom print commands. Its examples were compiled separately without the same enforced escape/axiom checks. The original invoice transcript also claimed an omitted-signature mutation that the script did not implement.

The repaired `proof/check.sh` delegates to `audit.py`, which:

- discovers every repository Lean file recursively outside Git metadata;
- scans all of those files, including examples, for the prohibited proof tokens;
- checks the Lean 4.19.0 toolchain and compiles fresh copied sources with warnings as errors, isolated from stale repository object files or inherited import paths;
- enumerates theorem declarations from the imported Lean environment by their source module, including generated and private theorems, rather than trusting a manually maintained print list;
- computes every theorem's transitive axiom dependencies and permits exactly `{propext, Quot.sound}`;
- records SHA256 hashes of the Lean sources, gate/audit scripts, toolchain pin, and bridge mutation.

The gate uses the repository's existing flat module names; duplicate or unsupported module basenames fail closed. It does not claim to be a universal package-manager replacement. Its audit counts theorem declarations; compiler-generated runtime auxiliary constants are not additional authored proof axioms.

The platform audit now includes all three proof modules and compiles from fresh copies. Its zero-word-hit result is a supplementary lexical check, not an argument that real platforms generate faithful witnesses.

The refreshed `examples/verification.txt` contains actual output from the current script. It no longer asserts the nonexistent omitted-signature mutation. The real wrong-middle-bridge mutation remains in `examples/range-ledger/mutation.patch` and is executed both through the aggregate examples gate and its standalone gate.

Fresh commands, all exiting 0:

```sh
LEAN=/path/to/lean sh proof/check.sh
LEAN=/path/to/lean sh examples/check.sh
LEAN=/path/to/lean sh examples/range-ledger/check.sh
LEAN=/path/to/lean python3 proof/platform-audit.py
```

Complete outputs are committed in [CHECK.log](CHECK.log), [examples/verification.txt](../examples/verification.txt), [range-ledger/verification.txt](../examples/range-ledger/verification.txt), and [PLATFORM-AUDIT.log](PLATFORM-AUDIT.log). The exact quoted gate endings and example output follow in the receipt appendix.

## Receipt appendix

The complete console output of the main gate and both examples invocations is pasted below. The main gate keeps its complete statement and dependency transcript in `CHECK.log`; its console output is a reproducible summary. The manifest can be checked from the repository root with `sha256sum -c proof/SOURCE-SHA256.txt`.

### `sh proof/check.sh` — exit 0

```text
Lean (version 4.19.0, x86_64-unknown-linux-gnu, commit 6caaee842e94, Release)
Repository Lean files: 5
Compiled: examples/InvoiceTrace.lean
Compiled: examples/range-ledger/BridgeRepair.lean
Compiled: proof/Traceability.lean
Compiled: proof/Controls.lean
Compiled: proof/ReturnControls.lean
Kernel theorem audit: 123 theorem declarations (including generated declarations)
Axiom subset check passed: every repository theorem uses only [propext, Quot.sound]
Axioms printed: [propext, Quot.sound]
Gate passed: 5 Lean files, warnings as errors, fresh imports, no prohibited proof tokens
Full proof transcript: proof/CHECK.log
Checked source hashes: proof/SOURCE-SHA256.txt
```

New theorem dependency lines from `CHECK.log`:

```text
'Traceability.contributor_isSome' depends on axioms: [propext, Quot.sound]
'Traceability.contributor_sound' depends on axioms: [propext]
'Traceability.returns_recorded_edge_weaker' depends on axioms: [propext, Quot.sound]
'Traceability.returns_recorded_head' depends on axioms: [propext]
```

### `sh examples/check.sh` — exit 0

```text
Lean (version 4.19.0, x86_64-unknown-linux-gnu, commit 6caaee842e94, Release)
(8,
 [InvoiceTrace.Event.override, InvoiceTrace.Event.signature],
 [InvoiceTrace.Event.quote, InvoiceTrace.Event.tax, InvoiceTrace.Event.currency])
'InvoiceTrace.extraction_exact' depends on axioms: [propext, Quot.sound]
'InvoiceTrace.preserves_verdict' depends on axioms: [propext, Quot.sound]
'InvoiceTrace.least_support' depends on axioms: [propext, Quot.sound]
'InvoiceTrace.before_after' does not depend on any axioms
'InvoiceTrace.route_is_needed' does not depend on any axioms
Lean (version 4.19.0, x86_64-unknown-linux-gnu, commit 6caaee842e94, Release)
(some 7, none)
'RangeLedger.BridgeRepair.returned_cut' depends on axioms: [propext, Quot.sound]
'RangeLedger.BridgeRepair.cut_distinguishes' depends on axioms: [propext, Quot.sound]
'RangeLedger.BridgeRepair.two_never_enough' depends on axioms: [propext]
'RangeLedger.BridgeRepair.ambiguity' depends on axioms: [propext, Quot.sound]
'RangeLedger.BridgeRepair.three_suffice' depends on axioms: [propext, Quot.sound]
'RangeLedger.BridgeRepair.bad_three' depends on axioms: [propext]
Rejected control: use the wrong middle bridge for the chain decoder.
```

### `sh examples/range-ledger/check.sh` — exit 0

```text
Lean (version 4.19.0, x86_64-unknown-linux-gnu, commit 6caaee842e94, Release)
(some 7, none)
'RangeLedger.BridgeRepair.returned_cut' depends on axioms: [propext, Quot.sound]
'RangeLedger.BridgeRepair.cut_distinguishes' depends on axioms: [propext, Quot.sound]
'RangeLedger.BridgeRepair.two_never_enough' depends on axioms: [propext]
'RangeLedger.BridgeRepair.ambiguity' depends on axioms: [propext, Quot.sound]
'RangeLedger.BridgeRepair.three_suffice' depends on axioms: [propext, Quot.sound]
'RangeLedger.BridgeRepair.bad_three' depends on axioms: [propext]
Rejected control: use the wrong middle bridge for the chain decoder.
```

### Supplementary platform scan — exit 0

```text
Statement enumeration: 71 statements
Hits: 0
Platform audit: PASS
```

### Gate failure controls

These were run in isolated copies to exercise the two corrected coverage gaps: an unprinted theorem depending on `Classical.choice`, and a custom declaration in the examples directory. Both were rejected. This is a gate test, not an extra assumed proof rule.

```text
unprinted-choice: rejected, exit 1; RepositoryAudit.lean:9:0: error: Rejected: unprintedChoice depends on forbidden axiom Classical.choice | Rejected: kernel declaration audit failed
example-escape: rejected, exit 1; Rejected: prohibited proof token 'axiom': examples/GateProbe.lean:1
```
