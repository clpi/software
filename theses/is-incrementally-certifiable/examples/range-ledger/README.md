# Canceling corrections and exact certificate reuse

| Before | After |
|---|---|
| 8 tile totals recomputed | 2 totals change; 6 can be reused |

Apply +7 to sample 100 and −7 to sample 200. The net window total stays fixed. Among eight 64-sample tiles, only [64,128) and [192,256) change.

## Derivation

For any old world and arbitrary signed prefix displacement, reuse of an interval value is valid exactly when its endpoint displacements are equal. The two listed tiles provably have different new values. Each must be replaced if the output stores individual tile totals.

## Replay

From the repository root run `sh examples/check.sh` to check both example series. To run this case alone use `sh examples/range-ledger/check.sh`. The [Lean proof](CertificateReuse.lean) and [verification transcript](verification.txt) record the positive result and a rejected semantic mutation.

## Scope

This bound counts replaced scalar values. Verifying a displacement, acquiring the edit log, or independently renewing an epoch-attestation carries its own cost.
