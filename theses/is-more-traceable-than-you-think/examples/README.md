# Extracting the premises of an actual invoice approval

| Before | After |
|---|---|
| 8 journal events to inspect | 2 or 3 supporting events, according to the recorded route |

The same journal contains an override and its signature as well as a quote, tax decision, and currency observation. Its route tag records which approval actually ran. The extractor filters the journal by the dependencies of that route.

## Why the bound holds

Lean proves exact membership and verdict preservation for arbitrary journals. Every alternative supporting the chosen route must contain every extracted premise in this complete journal. Approval alone is identical for both routes and cannot recover which premise set was used. Choosing the shorter override for a pricing approval would be wrong.

## Replay

Run from the repository root with Lean 4.19.0 available.

```sh
sh examples/check.sh
```

The runner checks the [proof](InvoiceTrace.lean) with warnings as errors and prints the computed result and theorem dependencies.

The [verification transcript](verification.txt) includes the observed outputs and the rejected counterexample mutation.

## Scope

This fixture has one event per kind, one invoice, and a trusted route tag. The scan-based extractor still reads the journal; the saving is in evidence presented for inspection. Production correlation, timestamps, and event authentication need their own contracts.

## Additional worked example

[Restore tracing across disconnected telemetry islands](range-ledger/README.md)
