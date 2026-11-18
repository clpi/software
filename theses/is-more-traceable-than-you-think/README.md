# Software is more traceable than you think

## The claim

Every execution of software appends witnesses to an append-only ledger. The accounting is a pure fold, so the historical witness hypergraph is a function of the witness set alone, independent of arrival order and of time. Witnesses carry exact time. The grain is the symbol, refined to the derivation step wherever a provable return needs it. A return is provable when the exact premise set of any witnessed outcome is derivable from the hypergraph alone. The construction holds independent of operating system, software, and language, because foreign executions enter through lifting plus kernel-boundary sensing.

## The parts and their evidence states at creation

Evidence states use the four states of this family: settled intent, proposed, implemented, and verified. Nothing in this file claims a part is verified before its artifact and check land in this repository.

- The claim: settled intent. This is the ruling of Chris, dated 2026-11-18.
- The hypergraph establishment over the real witness store: implemented in a lane and not yet landed in this repository. The store holds 2,509 witnesses, snapshot sha256 673ab30b1bea3bc98cd42ea68b1e1b58d3194891bb021b3f7b8949c7085e2c7e.
- The grain map: proposed. Its executed check is not yet landed.
- The Lean proof of platform independence: implemented in a lane and not yet landed in this repository.

## The sources of record

- The living spec in the Idol workspace records: "spec-decidability-engine-2026-11-17", sections 17 and 18.
- The sibling proof repository "clpi/software-is-quantifiable", which proves the fold at the accounting level.
- The sibling proof repository "clpi/software-optimality", which proves the incremental hypergraph semantics.

This repository proves the witness-stream level and platform independence. It does not re-prove the results of the sibling repositories.
