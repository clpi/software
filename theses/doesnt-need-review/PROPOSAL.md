# Proposal

Manual review is not dropped unconditionally. The process below replaces a review criterion only when it is a decidable predicate on the finite per-symbol profile, and only where two premises hold: the spec axes are the intended axes, and coverage holds for the named roster.

## Process

Each review criterion is disposed of in one of three ways.

- A decidable predicate on the finite per-symbol profile becomes a certifier axis. The axis refuses a symbol by name. The decision is the corresponding row of a table of size `2^n`, where `n` is the number of status cells in the profile.
- A semantic property of a program does not become a total axis. It is recorded as a named open spec premise.
- The same semantic property may be approximated by a decidable profile predicate. The certifier may run that predicate, and the gap stays named on the disposition. Naming the gap is part of the result.

The pass is structural recursion on a finite list, so it terminates, and each input criterion has one disposition.

## Preconditions

- Spec. The watched axes are exactly the intended axes (`SpecRight`), and every intended cell is observed (`CellsObserved`). These are premises.
- Coverage. Every execution on the named roster has a validated ledger record (`PlatformPremise`, projected by `coverage`). An identifier witness is not that record. `CellsObserved` does not discharge `PlatformPremise`. This is a premise, the coverage premise of software-is-quantifiable.

Outside those premises the certifier can accept a release that is bad on an unwatched cell. A reviewer who knows that cell catches it. That boundary is proved.

## What stays human

Writing specs: stating a new criterion. Also any semantic property that has not been reduced to a profile predicate, including the judgment of whether a named approximation gap is acceptable.

## Falsifiable

- A profile predicate whose value is not the row of its finite table.
- A mechanized axis that a later extension drops.
- A roster execution with no validated ledger record.
- A watched bad cell that the certifier does not refuse by name.
- A semantic criterion disposed of as a total axis, or an approximation whose gap was erased.

## Limit

Non-trivial semantic properties of programs are undecidable in general. They cannot be mechanized as total certifier axes. Rice, H. G., Classes of recursively enumerable sets and their decision problems, Transactions of the American Mathematical Society 74 (1953), 358–366. This repository does not formalize that theorem. The process above is the restriction: such a criterion stays human, or a named premise, or a decidable profile approximation with the gap named.

## Not measured

How often human review rubber-stamps a diff is not a theorem of this repository. No rate is claimed.
