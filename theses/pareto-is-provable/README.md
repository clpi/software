# Pareto optimality, proved for the general definitions

Machine-checked Lean 4.19.0 proofs of obligations 1 to 9 and 14
of the Pareto proof methodology record of 2026-11-22, over that
record's section 0 definitions (D1 to D11) with its premise
registry (P1 to P4) kept explicit and never discharged. This
repo is the proof home named for this program through the Jev
decision route (verdict row D-0018 in the pipeline decision log,
deterministic primary, confidence 1.0): a new dedicated repo,
because the quantifiable repo is the update and checker spine
program's home and the optimality repo is a separate active
program with its own cost model.

## Reproduce

```sh
LEAN=/path/to/lean-4.19.0 ./check.sh
```

The gate compiles from source on every run (cold), scans for
placeholder proof steps, audits axioms (at most the standard
three: propext, Classical.choice, Quot.sound), runs the
hypothesis and naming audit, and runs its standing control:
the audit must refuse the draft in the controls folder that
states finiteness as a hypothesis.

## Home record — lane 1 closure at the landing pin

Closing pin: the head commit of this repo at landing, named in
the lane record (research folder, pareto lane 1 record of
2026-11-22). Version tuple: table pin 9 (the test instance);
solver verdict version 1; checker reading version 1; instrument
versions 1 on both test axes; Lean 4.19.0, release commit
6caaee842e94. Axiom audit at the closing pin: every theorem
below depends on no axioms, or on a subset of the standard
three; none on anything else. Gate output: compile exit 0,
zero placeholders, audit control passed.

| Obligation | Theorem | Evidence beyond the proof |
|---|---|---|
| 1 enumeration | one.enumeration, one.unique | checker pass on the instance and refusal on a row-missing table (tests.space) |
| 2 entry | two.ledger | checker pass on a four-presentation log with one duplicate refusal (tests.logtest) |
| 3 finiteness | three.finiteness | derived from the declaration lists, no hypothesis; hypothesis audit refuses the controls draft |
| 4 change | four.change | instance step executed (tests.step) |
| 5 declared | five.declared, five.timing | checker passes on the instance (tests.declared, tests.timing) |
| 6 binding | six.binding (hypotheses P1, P2) | agreement test: instrument re-run reproduces every cell (tests.bind) |
| 7 receipts | seven.receipted | control: one receipt removed yields UNMEASURED naming that cell, from the cone procedure, accept from none (tests.gap) |
| 8 fixed | eight.fixed, eight.versioned, eight.invalidated | control: one axis direction reversed on a copy; invalidation set computed and receipted by the test (tests.touch) |
| 9 pairwise | nine.pairwise, nine.crossiff, nine.agree (hypothesis P2) | differential test over the full pair set of the instance, nine ordered pairs, including all-equal and one-axis-difference pairs (tests.agree, tests.equal, tests.single, tests.self) |
| 14 locality | fourteen.locality | proved from D5 and D8: the verdict is a function of the two rows alone |

States kept separate, per the methodology record: these are
verified behaviors at the landing pin for the general
definitions. No instance claim (lane 3 onward) is made here.
Obligations 10 to 13 and 15 to 20 are lane 2 and are not
claimed in this repo yet.
