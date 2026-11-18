# How many paired loads certify an affine cost comparison?

| Before | After |
|---|---|
| 4,097 paired loads from 0 through 4,096 | 2 paired endpoint loads |

Compare candidate minus incumbent cost at empty and full load. Under an independently justified affine cost law, both endpoint gaps being nonpositive is equivalent to non-regression at every integer load between them.

## Derivation

At any single chosen load, a zero gap is consistent with another affine gap that agrees there and is positive elsewhere. Thus no one-sample procedure can always decide this contract exactly. A nonlinear interior spike passes both endpoints and violates the claim at load 2,048.

## Replay

From the repository root run `sh examples/check.sh` to check both example series. To run this case alone use `sh examples/range-ledger/check.sh`. The [Lean proof](AffineCalibration.lean) and [verification transcript](verification.txt) record the positive result and a rejected semantic mutation.

## Scope

An exact affine law and exact paired cost observations. No claim of measured runtime affinity or statistical confidence is made. Noisy machine timings require a sampling and model-validation contract.
