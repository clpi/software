# Solve a total from overlapping snapshots

| Before | After |
|---|---|
| 4,096 source values | 3 retained scalar receipts |

The available windows are [0,3072), [1024,3072), and [1024,4096). They need neither disjoint boundaries nor a shared partition layout.

## Derivation

Add the outer two and subtract the overlap. The cancellation holds for every integer prefix potential. For each omitted receipt, Lean constructs a second world agreeing on the other two and changing the total. All three are necessary. Adding all three produces 260 where the fixture requires 160.

## Replay

From the repository root run `sh examples/check.sh` to check both example series. To run this case alone use `sh examples/range-ledger/check.sh`. The [Lean proof](OverlapPlan.lean) and [verification transcript](verification.txt) record the positive result and a rejected semantic mutation.

## Scope

One immutable snapshot, one unit, and exactly the three declared scalar receipt types. Generation or acquisition costs are separate. The family synthesis charges an index build explicitly.
