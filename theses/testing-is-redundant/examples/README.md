# Checking a capacity limit at its two boundaries

| Before | After |
|---|---|
| 256 load probes | 2 probes, at 127 and 128 |

The required policy accepts load up to 127 and rejects larger loads. Assume independently established downward closure of the implementation’s admission decision. Probe the last accepted load and the first rejected load.

## Why the bound holds

Monotonicity propagates the two outcomes to every natural-number load. The repository’s acceptance theorem shows the 256-case suite contributes no further constraint. Every exact suite on the threshold family needs both neighbors: cutoffs 126 and 128 differ from the target at just one point each. A non-monotone hole at load 40 passes both probes and violates the policy.

## Replay

Run from the repository root with Lean 4.19.0 available.

```sh
sh examples/check.sh
```

The runner checks the [proof](QuotaBoundary.lean) with warnings as errors and prints the computed result and theorem dependencies.

The [verification transcript](verification.txt) includes the observed outputs and the rejected counterexample mutation.

## Scope

Downward closure must be justified separately for the implementation and venue. The optimization is for the threshold contract; a richer behavior specification can require more observations.
