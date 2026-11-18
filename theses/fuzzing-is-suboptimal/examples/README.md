# Covering every accepted command in a finite frame format

| Before | After |
|---|---|
| 256 calls over the raw two-nibble grid | 16 calls, one per command |

A frame contains a four-bit command and its one’s complement. The target is to exercise every successfully decoded command. The encoder supplies the only valid second nibble for each first nibble.

## Why the bound holds

The inverse theorem covers every natural-number pair supplied to the decoder. The two campaigns reach exactly commands 0 through 15 in order. Each invocation returns at most one command, so any covering campaign requires at least 16 calls. If malformed-input rejection becomes a goal, the valid-only campaign omits it.

## Replay

Run from the repository root with Lean 4.19.0 available.

```sh
sh examples/check.sh
```

The runner checks the [proof](FrameCampaign.lean) with warnings as errors and prints the computed result and theorem dependencies.

The [verification transcript](verification.txt) includes the observed outputs and the rejected counterexample mutation.

## Scope

The baseline is exhaustive raw enumeration, and the objective is distinct successful commands. The example makes no estimate of random-fuzzer runtime or fault-finding power.

## Additional worked example

[Generate one interval per actual routing behavior](range-ledger/README.md)
