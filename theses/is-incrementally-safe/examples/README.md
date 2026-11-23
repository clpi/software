# Requalifying a release after a policy rewrite

| Before | After |
|---|---|
| 4 rule evaluations in a clean rebuild | 2 fresh evaluations and 2 valid cached values |

One gate migrates from a legacy approval to its replacement. The replacement fact also changes. The old verdict vector is [true, true, true, false]. The new vector is [false, true, false, false].

## Why the bound holds

The structural read set is derived from each conjunction or disjunction. A cached verdict is reusable when the rule is equal and its read values agree. Lean proves equality with a clean rebuild for arbitrary rule lists, including additions and removals. Here both recomputed slots actually flip, so any strategy that reuses old slot values must replace at least those two. Holding all source values fixed can still change a verdict when the rule is rewritten.

## Replay

Run from the repository root with Lean 4.19.0 available.

```sh
sh examples/check.sh
```

The runner checks the [proof](PolicyMigration.lean) with warnings as errors and prints the computed result and theorem dependencies.

The [verification transcript](verification.txt) includes the observed outputs and the rejected counterexample mutation.

## Scope

Rows are positional in this example. Reuse requires a correct original cache and pure evaluations of the declared facts. Work units are fresh rule evaluations; checking equality and reading the cache also cost work.

## Additional worked example

[Apply a telemetry row move without scanning both groups](range-ledger/README.md)
