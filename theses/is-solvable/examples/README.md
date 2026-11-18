# Minimum-cost restore qualification

| Before | After |
|---|---|
| 8 work units, two separate tests | 6 work units, one combined run |

An immutable snapshot is already recorded. A checksum plus the snapshot derives integrity. Integrity plus replay evidence derives restorability. The available checks cost 3, 5, or 6 units; the combined lab run supplies both missing roots.

## Why the bound holds

The kernel checks every subset of the three purchasable tests against the repository’s bounded hypergraph closure. Six is the minimum cost of a successful plan. Unioning the two precomputed closures misses the mixed-premise derivations. A checksum alone cannot establish restorability.

## Replay

Run from the repository root with Lean 4.19.0 available.

```sh
sh examples/check.sh
```

The runner checks the [proof](RestoreEvidence.lean) with warnings as errors and prints the computed result and theorem dependencies.

The [verification transcript](verification.txt) includes the observed outputs and the rejected counterexample mutation.

## Scope

The three prices and the transfer rules are declared fixture inputs. Applying the conclusion to a backup system requires justified rules, scoped receipts, and the actual available test menu.
