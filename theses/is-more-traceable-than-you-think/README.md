# Software is more traceable than you think

## The intended claim and the proven boundary

The design goal is to retain software's execution witnesses in an append-only ledger and recover the exact recorded premises of outcomes at symbol or derivation-step grain. Connecting real executions to complete, truthful witnesses remains a separate sensing and lifting obligation.

The generic Lean model proves that the hypergraph fold preserves exactly the nodes and complete derivation records supplied by an arbitrary lifting. Its graph is independent of event order and repeated presentation; the timed fold also ignores its separate `Timed.time` field. An underlying event and its lifting may themselves retain time data. Filtering the stream retracts contributions exactly. The executable `contributor` search succeeds exactly when the queried complete derivation is present in the fold, and returns an actual contributing event from the retained stream. It does not reconstruct that stream or erased `Timed.time` fields from the graph.

A witnessed head alone does **not** guarantee a derivation under an arbitrary lifting. The former `returns_head` assumed a contribution equivalent to its conclusion and ignored its witnessed-head hypothesis; it has been removed. Its general replacement is explicitly named `returns_recorded_edge_weaker`. The narrower `returns_recorded_head` proves head recovery for `recordLift`, which constructs the head and its exact derivation together, with explicit equality decisions. This theorem uses the witnessed-head hypothesis and returns some recorded derivation, without promising unique or causally valid premises.

The [two-voice proof review](proof/REPORT.md) gives the exact statements, standing counterexamples, answers to every attack, and the proves/cannot-say lists. The boundary is exercised by ten additional [return controls](proof/ReturnControls.lean).

## The parts and their evidence states

Evidence states use the four states of this family: settled intent, proposed, implemented, and verified. The snapshot execution evidence below was recorded when those parts landed on 2026-11-18; the return-proof repair does not rerun that separate data pipeline. The Lean statements and receipts describe the sources in this revision.

- The claim: settled intent. This is the ruling of Chris, dated 2026-11-18.
- The hypergraph establishment over the real witness store: verified at the frozen snapshot, and landed in the folder named hypergraph. The snapshot holds 2,509 witnesses and 8,482 recorded join edges (sha256 673ab30b1bea3bc98cd42ea68b1e1b58d3194891bb021b3f7b8949c7085e2c7e); the built hypergraph holds 20,480 nodes and 9,356 hyperedges (sha256 a847fb5465f743700f90b34b423444fa8441660b6854c53cd8f62aea58829ea5). Its construction was executed four times — as filed, twice, on a shuffled feed, and on a duplicated feed — with byte-identical output, and its 719 classes were re-derived from the hypergraph alone, identical. Exact time in this store is the batch and its step index: the records carry no timestamp field, and the establishment report says plainly what time the store does and does not carry.
- The grain map: verified by execution at the same snapshot, and landed in the folder named returns. Of 1,526 accounting entries, 1,522 have provable returns at symbol grain and 4 at derivation-step grain, with none failing. The one refinement site is the repeated-observation pair in the idol-prof battery class, named in full in the grain map.
- The Lean proof: the generic fold and executable contributor statements above are proven for arbitrary supplied liftings; head recovery is proven only for the explicit `recordLift` construction. The repository-wide gate compiles every Lean file with warnings as errors, rejects proof escapes, and audits every theorem's transitive dependencies against exactly `{propext, Quot.sound}`. See [CHECK.log](proof/CHECK.log), [source hashes](proof/SOURCE-SHA256.txt), and the [fresh baseline receipts](proof/receipts/). A mechanical platform-word scan is supplementary evidence, not a proof that real executions emit complete witnesses.
- A worked example: the folder named examples carries a checked before-and-after trace example, added by Chris.

## The sources of record

- The living spec in the Idol workspace records: "spec-decidability-engine-2026-11-17", sections 17 and 18.
- The sibling proof repository "clpi/software-is-quantifiable", which proves the fold at the accounting level.
- The sibling proof repository "clpi/software-optimality", which proves the incremental hypergraph semantics.

This repository proves the witness-stream level and platform independence. It does not re-prove the results of the sibling repositories.

## Replay

With Lean 4.19.0 available, run `sh proof/check.sh`, `sh examples/check.sh`, and `sh examples/range-ledger/check.sh`. Set `LEAN=/path/to/lean` when needed. The examples gate includes the range-ledger gate and its rejected wrong-bridge mutation; the standalone invocation permits replaying it independently. Run `python3 proof/platform-audit.py` for the supplementary statement scan.
