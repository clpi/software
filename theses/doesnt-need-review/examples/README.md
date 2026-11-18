# Which schema migrations need an owner decision?

| Before | After |
|---|---|
| 6 owner decisions | 2 owner decisions, 4 automatic verdicts |

The owner policy requires the current reader to pass and any still-active legacy reader to work. CI reports whether the patch drops a column and whether current-reader tests pass. The hidden fact is whether all legacy readers have retired.

## Why the bound holds

For every possible report, the classifier escalates exactly when the two retirement states yield different policy decisions. Every automatic verdict is sound. Any decision process using the same two fields must defer on those ambiguous reports. The SQLite replay executes six migrations under both reader populations and compares the outcomes with the classifier.

## Replay

Run from the repository root with Lean 4.19.0 and Python 3 available.

```sh
sh examples/check.sh
```

The runner checks the [proof](MigrationReview.lean) with warnings as errors and prints the computed result and theorem dependencies. It then runs the [independent execution](replay.py).

The [verification transcript](verification.txt) includes the observed outputs and the rejected counterexample mutation.

## Scope

The lower bound is the number of ambiguous reports, assuming an independent retirement fact per change. A trusted retirement record or shared evidence across changes changes that bound. SQLite 3.35+ is required for DROP COLUMN.
