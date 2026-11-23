# Apply a telemetry row move without scanning both groups

| Before | After |
|---|---|
| Reaggregate both affected groups from their rows | 2 group-total replacements |

A 19-unit row moves from group 2 into group 3 with value 24. Totals 100 and 90 become 81 and 114. Direct insertion and deletion are the same operation with an absent old or new image.

## Derivation

The splice theorem holds for arbitrary lists surrounding the edit and every group. Subtract the old row contribution and add the new row contribution. Both outputs actually change, forcing two scalar replacements. Old values 19 and 20 give different answers with the same new image and cached old total.

## Replay

From the repository root run `sh examples/check.sh` to check both example series. To run this case alone use `sh examples/range-ledger/check.sh`. The [Lean proof](GroupedEdits.lean) and [verification transcript](verification.txt) record the positive result and a rejected semantic mutation.

## Scope

The transaction supplies the actual before-image and is applied once against its matching cached snapshot. The theorem covers exact signed totals; acquisition, replay detection, and atomic publication are upstream obligations.
