# The minimum exact basis for every interval query

| Before | After |
|---|---|
| 8,390,656 nonempty windows | 4,096 singleton probes |

Assume the implementation is additive on adjacent ranges, established independently. Agreement on each singleton implies agreement on every contiguous nonempty interval. The replay compares all windows of a real 4,096-element fixture with a separately computed prefix oracle.

## Derivation

The lower bound permits arbitrary fixed interval probes, including probes outside the named window. Begin with one independent prefix offset per endpoint. Each scalar interval measurement can merge at most two classes. To identify every unit difference along n samples takes at least n measurements. Omitting singleton i hides a step at exactly i.

## Replay

From the repository root run `sh examples/check.sh` to check both example series. To run this case alone use `sh examples/range-ledger/check.sh`. The [Lean proof](IntervalBasis.lean) and [verification transcript](verification.txt) record the positive result and a rejected semantic mutation. The runner also executes the [independent replay](replay.py).

## Scope

Universal exactness over additive integer worlds, with fixed nonadaptive probes. Extra trusted information can reduce the required basis. A single fixture cannot establish additivity of an arbitrary implementation.
