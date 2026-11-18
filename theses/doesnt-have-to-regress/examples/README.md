# Minimum writes for an ordered fixed-record log

| Before | After |
|---|---|
| 4,096 successful single-record writes | 64 successful writes, 16,384 identical bytes |

Each record carries its sequence number as a four-byte integer. The writer may send up to 64 records in one operation. It sends full chunks and one final partial chunk if required.

## Why the bound holds

The content theorem covers arbitrary ordered input lists, including empty input. Each legal batch has length at most 64. The constructed packing achieves the capacity lower bound against every competing partition with identical flattened contents. The POSIX replay counts write calls to a fresh regular file, checks every byte against the original input, and probes both sides of the chunk boundary.

## Replay

Run from the repository root with Lean 4.19.0 and Python 3 available.

```sh
sh examples/check.sh
```

The runner checks the [proof](LogBatching.lean) with warnings as errors and prints the computed result and theorem dependencies. It then runs the [independent execution](replay.py).

The [verification transcript](verification.txt) includes the observed outputs and the rejected counterexample mutation.

## Scope

The measured venue completed every requested write in full. The contract compares final byte sequences on a single-writer file. Per-record acknowledgment, crash visibility, competing writers, and partial-write recovery would change the contract.
