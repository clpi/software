# Choose a tile size that minimizes worst-case read work

| Before | After |
|---|---|
| 4,096 worst-case reads in the raw layout | 64 worst-case reads with 64 × 64 tiling |

A full-window query reads one total per tile. Rebuilding one dirty tile reads every raw value in that tile. A uniform exact covering of 4,096 values has r tiles of s values with r × s = 4,096.

## Derivation

Every feasible (r,s) is Pareto-nondominated on these two axes. If both costs were at most 63 their product would fall below 4,096. The square layout reaches 64 exactly and minimizes the worse operation. A trusted value delta changes the refresh cost and can change the winner.

## Replay

From the repository root run `sh examples/check.sh` to check both example series. To run this case alone use `sh examples/range-ledger/check.sh`. The [Lean proof](TileFrontier.lean) and [verification transcript](verification.txt) record the positive result and a rejected semantic mutation.

## Scope

Uniform exact tilings, one dirty tile, a stored total per tile, no usable edit delta, and unit logical reads. Query and refresh are separate operations.
