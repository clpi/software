# Tight flush bound for a 16-bit telemetry accumulator

| Before | After |
|---|---|
| 64 flushes per 4,096 bytes at width 64 | 16 flushes at the maximum safe width of 257 |

Unsigned samples range from 0 to 255. A local lane wraps modulo 65,536. Flush it into an exact wide total after at most 257 bytes.

## Derivation

257 × 255 = 65,535. Every legal chunk is exact; combining legal chunks preserves the complete sum. A 258-byte all-255 chunk should yield 65,790 and wraps to 254. At least 16 flushes are necessary under the fixed worst-case capacity, and 15 full chunks plus one partial chunk attain it.

## Replay

From the repository root run `sh examples/check.sh` to check both example series. To run this case alone use `sh examples/range-ledger/check.sh`. The [Lean proof](AccumulatorBudget.lean) and [verification transcript](verification.txt) record the positive result and a rejected semantic mutation. The runner also executes the [independent replay](replay.py).

## Scope

This is the unsigned-byte ingestion stage. The downstream signed telemetry model also permits negative corrections. The optimality bound is for a fixed input-independent safe cap, with one lane and one counted flush per chunk.
