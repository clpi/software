# Historical admission model

These two files are an isolated, reproducible copy of the model identified in the
2026-11-18 audit. They support the counterexample controls and the precise repair
of the historical claim. They do not replace the active family interface or its
current dependencies.

## Source pins

Repository: `clpi/software-is-incrementally-safe`

Commit: `de1b30716e2b758141d5940056f37cd678464032`

| Local module | Original path | Original Git blob SHA-1 |
|---|---|---|
| `Legacy/SoftwareIsComposable.lean` | `SoftwareIsComposable.lean` | `251c0824e8bc48a82bc69a640cbd54d7aff86f63` |
| `Legacy/SoftwareIsIncrementallyCertifiable.lean` | `SoftwareIsIncrementallyCertifiable.lean` | `28f33d5fefa1a54e426a5ef45030be2f64794dee` |

The certifiable source identifies the audited repository pin
`f3b9f896ac76a95e7104c98af66e41413e7e5b2d` in its `siblingPin`. That repository
pin contains only its README. Its copied module was available in the safe
repository at the source commit above.

To reproduce each local module from its original UTF-8 contents, perform exactly
these two literal substitutions, in order:

1. `SoftwareIsComposable` becomes `Legacy.SoftwareIsComposable`.
2. `SoftwareIsIncrementallyCertifiable` becomes
   `Legacy.SoftwareIsIncrementallyCertifiable`.

There are no mathematical changes. The substitutions isolate namespaces and
resolve the import to the historical copy; the final newline is retained. The
inverse substitutions recover both original blobs exactly. Both archival modules
are compiled by the repository gate with warnings as errors.

## What is imported

`Profile`, `profileLE`, and the profile order laws come from the first file.
`c`, its closure laws, `Cost`, `paretoLE`, `paretoDominates`, `Admission`, `admits`,
and `admitted_downward` come from the second file.

The historical order is directional: `profileLE p q` means every observation
in `p` is in `q`. Therefore `admitted_downward` permits behavior deletion.
Historical `c` is this downward closure. It is not identified with the current
family's rule-derivation closure `Qualification.Derives`.

## Missing lemma and proved repair

`IncrementalCert/LegacySequence.lean` proves:

- `cost_adjacent_iff_global`: adjacent cost nonregression is necessary and
  sufficient for nonregression between every pair of chronologically ordered
  releases. Admission is absent from this theorem because it does not establish
  the needed adjacent comparison.
- `admitted_sequence`: initial admission plus the two existing
  `admitted_downward` hypotheses at each step preserves admission for an arbitrary
  sequence. `release_sequence` adds all-pairs cost nonregression and rules out
  strict reverse dominance.
- `rechecked_sequence`: independently admitted releases need no downward profile
  hypothesis. Add adjacent cost nonregression and preservation of fixed required
  observations, and all releases retain those requirements and cannot regress
  against any earlier release.
- `GuardedStep` and `guarded_sequence`: a separately named transition guard adds
  adjacent cost comparison and fixed requirement preservation to the unchanged
  historical `admits` predicate. It allows new optional observations when the
  later release independently passes admission.
- `paretoLE_antisymm`: mutual cost comparison means identical `Cost` values.
  The original source exported only a preorder, but its actual natural-number
  product order is antisymmetric. Different artifacts or profiles with equal
  costs remain possible.
- `strict_interval_iff`: along a weakly improving chain, the endpoint costs are
  strictly better exactly when at least one intervening step is strictly better.
  `strict_interval_no_return` and `return_forces_constant_interval` exclude strict
  cost cycles and characterize weak cycles as constant-cost intervals.
- `required_adjacent_iff_global`: with initial coverage, required-only retention
  at every step is equivalent to coverage at every release. The requirement
  predicate is fixed; optional observations need not be retained.

These results do not derive improvement from admission, do not claim that every
step is strict, and do not claim global Pareto optimality over candidates outside
the declared history. In particular, downward safety closure, cost order, and
positive behavior obligations remain distinct.
