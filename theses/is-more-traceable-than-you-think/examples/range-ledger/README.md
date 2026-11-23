# Restore tracing across disconnected telemetry islands

| Before | After |
|---|---|
| 6 pairwise bridge readings across 4 islands | 3 bridges in a spanning chain |

Each island has internally consistent readings and an unknown prefix offset. Recover every relative offset. A three-edge chain permits direct reconstruction up to the common origin.

## Derivation

For every choice of at most two wires, the checker produces a nonconstant offset assignment on which every chosen wire reads zero. The zero world produces the same transcript. Three edges attain the lower bound only with the right topology: a triangle leaves the fourth island unobservable.

## Replay

From the repository root run `sh examples/check.sh` to check both example series. To run this case alone use `sh examples/range-ledger/check.sh`. The [Lean proof](BridgeRepair.lean) and [verification transcript](verification.txt) record the positive result and a rejected semantic mutation.

## Scope

Four source components, pairwise exact differences, and stable endpoint identity. Absolute offset still requires an independent anchor.
