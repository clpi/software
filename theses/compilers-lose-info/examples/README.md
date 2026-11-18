# Minimum provenance for a constant-folded quote

| Before | After |
|---|---|
| 1 emitted price for 4 distinct origins | 2 side bits recover both origin choices |

Tariff and shipping may each come from an imported or local source. All four fixture quotes fold to 100. A downstream audit asks for the two origin choices while retaining the folded price.

## Why the bound holds

Any decoder using the price alone receives identical input for distinguishable origins. Lean also rules out every possible one-bit encoder/decoder pair. Carrying the two source bits suffices for every quote. The lower bound applies to fixed-width side information on this output fiber.

## Replay

Run from the repository root with Lean 4.19.0 available.

```sh
sh examples/check.sh
```

The runner checks the [proof](FoldedQuote.lean) with warnings as errors and prints the computed result and theorem dependencies.

The [verification transcript](verification.txt) includes the observed outputs and the rejected counterexample mutation.

## Scope

The recovered property is the pair of source-choice flags. Recovering all source text, constants, or an arbitrary provenance DAG would require a different observation contract.
