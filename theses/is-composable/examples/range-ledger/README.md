# Compose three interval certificates with a reversed seam

| Before | After |
|---|---|
| 4,096 source values to reconstruct the window | 3 signed receipts yielding 160 |

Two producers may give intervals oriented in opposite directions. The consumer can reverse the middle receipt, verify matching endpoints, and stitch the chain. For fixture values 120, 50, and 90 the result is 160.

## Derivation

Reverse preserves validity. Every successful finite chain produces the true difference between its recorded endpoints, assuming each input receipt is valid for the same world. The unreversed middle receipt fails the seam check. The companion overlap proof establishes that the three values are necessary in this catalog.

## Replay

From the repository root run `sh examples/check.sh` to check both example series. To run this case alone use `sh examples/range-ledger/check.sh`. The [Lean proof](SignedStitch.lean) and [verification transcript](verification.txt) record the positive result and a rejected semantic mutation.

## Scope

Producer validity, epoch, and unit alignment are premises. A matching numeric endpoint alone cannot authenticate a producer.
