# What must survive a SQL SUM rewrite?

| Before | After |
|---|---|
| Rescan nullable rows to distinguish NULL from zero | One signed sum and one presence bit per shard |

An empty or all-NULL shard and a shard containing +7 and −7 both have numeric sum zero. SQL must distinguish their outputs. The rewrite merges integer sums by addition and presence flags by OR.

## Derivation

For every finite list of nullable integers, the decoded summary equals the SQL-style fold. Merging independently summarized partitions is exact for every split. No decoder of numeric sum alone can distinguish the colliding inputs. One extra bit is sufficient and necessary for that ambiguity.

## Replay

From the repository root run `sh examples/check.sh` to check both example series. To run this case alone use `sh examples/range-ledger/check.sh`. The [Lean proof](NullableAggregate.lean) and [verification transcript](verification.txt) record the positive result and a rejected semantic mutation. The runner also executes the [independent replay](replay.py).

## Scope

The observable is SQL SUM with exact intermediate integer arithmetic. The physical SQLite cases fit its integer range. Other aggregates, order-dependent values, and overflow behavior need their own contract.
