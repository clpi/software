# Recertifying one edited leaf in a Merkle build tree

| Before | After |
|---|---|
| 2,047 SHA-256 calls per full rebuild | 11 SHA-256 calls per repaired tree |

A balanced binary manifest has 1,024 leaves. An edit changes one leaf. Its sibling subtrees already have valid cached receipts. The replay edits each of the 1,024 positions independently and checks every cached digest against a clean rebuild.

## Why the bound holds

Lean proves full-cache equality for every tree, path, payload, and pair of hash functions. A fresh receipt at each changed path level is the audit contract. Full construction and path repair report work from their recursive calls. A height-10 path contains 11 distinct required levels, so every complying receipt list must contain at least 11 entries. A leaf-only update misses the root.

## Replay

Run from the repository root with Lean 4.19.0 and Python 3 available.

```sh
sh examples/check.sh
```

The runner checks the [proof](MerkleRepair.lean) with warnings as errors and prints the computed result and theorem dependencies. It then runs the [independent execution](replay.py).

The [verification transcript](verification.txt) includes the observed outputs and the rejected counterexample mutation.

## Scope

The count covers hash calls for a single edit using an existing, valid cache. Cache acquisition, disk access, and multi-edit scheduling have separate costs. The equality proof requires no assumption about collision resistance.

## Additional worked example

[Canceling corrections and exact certificate reuse](range-ledger/README.md)
