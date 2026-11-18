# Software is more traceable than you think

## The claim

Every execution of software appends witnesses to an append-only ledger. The accounting is a pure fold, so the historical witness hypergraph is a function of the witness set alone, independent of arrival order and of time. Witnesses carry exact time. The grain is the symbol, refined to the derivation step wherever a provable return needs it. A return is provable when the exact premise set of any witnessed outcome is derivable from the hypergraph alone. The construction holds independent of operating system, software, and language, because foreign executions enter through lifting plus kernel-boundary sensing.

## The parts and their evidence states

Evidence states use the four states of this family: settled intent, proposed, implemented, and verified. Nothing in this file claims a part is verified before its artifact and check land in this repository. States below were updated when the parts landed, 2026-11-18.

- The claim: settled intent. This is the ruling of Chris, dated 2026-11-18.
- The hypergraph establishment over the real witness store: verified at the frozen snapshot, and landed in the folder named hypergraph. The snapshot holds 2,509 witnesses and 8,482 recorded join edges (sha256 673ab30b1bea3bc98cd42ea68b1e1b58d3194891bb021b3f7b8949c7085e2c7e); the built hypergraph holds 20,480 nodes and 9,356 hyperedges (sha256 a847fb5465f743700f90b34b423444fa8441660b6854c53cd8f62aea58829ea5). Its construction was executed four times — as filed, twice, on a shuffled feed, and on a duplicated feed — with byte-identical output, and its 719 classes were re-derived from the hypergraph alone, identical. Exact time in this store is the batch and its step index: the records carry no timestamp field, and the establishment report says plainly what time the store does and does not carry.
- The grain map: verified by execution at the same snapshot, and landed in the folder named returns. Of 1,526 accounting entries, 1,522 have provable returns at symbol grain and 4 at derivation-step grain, with none failing. The one refinement site is the repeated-observation pair in the idol-prof battery class, named in full in the grain map.
- The Lean proof of platform independence: proven, and landed in the folder named proof. The module proves order and time independence of the fold, provable returns, and retraction exactness, quantified over arbitrary events, nodes, times, and an arbitrary lifting. Its check gate passes with zero sorries; the printed axioms are propext and Quot.sound, both standard. The folder also carries the author's adversarial controls against weakened variants and a mechanical platform audit with zero hits.
- A worked example: the folder named examples carries a checked before-and-after trace example, added by Chris.

## The sources of record

- The living spec in the Idol workspace records: "spec-decidability-engine-2026-11-17", sections 17 and 18.
- The sibling proof repository "clpi/software-is-quantifiable", which proves the fold at the accounting level.
- The sibling proof repository "clpi/software-optimality", which proves the incremental hypergraph semantics.

This repository proves the witness-stream level and platform independence. It does not re-prove the results of the sibling repositories.
