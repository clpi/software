# Rerunning a benchmark with one changed shard

| Before | After |
|---|---|
| 8 shard runs | 1 fresh shard run |

Seven immutable, independently scoped shard receipts are reusable; shard 3 has changed. The campaign must account for each shard result at the required scope. Charge one unit per benchmark execution.

## Why the bound holds

The one-run plan covers every result required by the eight-run plan and strictly dominates it on run count. Any complete alternative needs shard 3. A zero-run reporter sees identical prior data whether the new shard value is 10 or 25, but the correct totals are 80 and 95.

## Replay

Run from the repository root with Lean 4.19.0 available.

```sh
sh examples/check.sh
```

The runner checks the [proof](ShardCampaign.lean) with warnings as errors and prints the computed result and theorem dependencies.

The [verification transcript](verification.txt) includes the observed outputs and the rejected counterexample mutation.

## Scope

The evidence model treats the seven scoped results as already validated. An independent fresh sample, changed venue, expired receipt, or stochastic measurement changes the obligation. Retrieval and aggregation time are outside the run-count objective.

## Additional worked example

[How many paired loads certify an affine cost comparison?](range-ledger/README.md)
