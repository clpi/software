# Eliminate canceled endpoint loads while preserving provenance

| Before | After |
|---|---|
| 6 endpoint occurrences in the source expression | 2 essential direct endpoint values |

Expand the signed union of three overlapping intervals into direct endpoint loads. The four distinct endpoint coefficients are −1, 0, 0, +1. The folded expression reads only endpoints 0 and 4,096.

## Derivation

Lean derives the exact change in any expression when endpoint i changes, for arbitrary perturbations. It then proves source/folded equality on every world and shows that every correct fixed set of direct reads must contain both outer endpoints. The zero coefficients explain why the inner endpoints can disappear from the value computation.

## Replay

From the repository root run `sh examples/check.sh` to check both example series. To run this case alone use `sh examples/range-ledger/check.sh`. The [Lean proof](LinearProvenance.lean) and [verification transcript](verification.txt) record the positive result and a rejected semantic mutation.

## Scope

Pure, exact integer potential reads with stable endpoint meanings. The contract preserves the numeric result. Observed effects of executing individual loads or their trace would be additional outputs.
