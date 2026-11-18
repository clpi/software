# Smallest safe checkout rebuild block

| Before | After |
|---|---|
| 5 services in one block | 3 services in the checkout block |

The modeled calls are checkout → invoice → tax and search → index. Placing checkout, invoice, and tax together allows the second component to stay independent while every call remains internal.

## Why the bound holds

Every interaction-closed partition must put invoice and tax with checkout. The exhibited partition achieves that inclusion lower bound. The repository’s composition theorem makes stubbed and linked evaluations agree for every export table and release under this partition. Splitting all five services into singletons accepts a changed tax export that the linked release rejects.

## Replay

Run from the repository root with Lean 4.19.0 available.

```sh
sh examples/check.sh
```

The runner checks the [proof](ReleasePartition.lean) with warnings as errors and prints the computed result and theorem dependencies.

The [verification transcript](verification.txt) includes the observed outputs and the rejected counterexample mutation.

## Scope

The objective counts services in the checkout block. The complete call list, stable IDs, and the repository’s export/behavior model define the scope. This example measures no build time.

The existing [old](old.csv) and [new](new.csv) CSV fixtures exercise per-symbol verdicts through the repository harness.

## Additional worked example

[Compose three interval certificates with a reversed seam](range-ledger/README.md)
