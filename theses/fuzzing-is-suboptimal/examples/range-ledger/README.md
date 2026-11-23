# Generate one interval per actual routing behavior

| Before | After |
|---|---|
| 2,145 legal intervals in a 64-sample window | 11 representatives |

The observed behavior is the sequence of 16-sample banks touched by a half-open interval. All empty intervals share one route. Each nonempty route is identified by its first and last bank.

## Derivation

The encoder realizes every reachable signature, and every legal input maps to the catalog. A single execution covers one signature, so any covering suite requires at least 11 executions. The replay enumerates actual visited positions independently. A width-sensitive oracle distinguishes inputs inside the same class.

## Replay

From the repository root run `sh examples/check.sh` to check both example series. To run this case alone use `sh examples/range-ledger/check.sh`. The [Lean proof](IntervalCampaign.lean) and [verification transcript](verification.txt) record the positive result and a rejected semantic mutation. The runner also executes the [independent replay](replay.py).

## Scope

One fixed window of four banks, all ordered endpoints including empty intervals, and bank routing as the sole coverage objective. It makes no universal claim about fault discovery.
