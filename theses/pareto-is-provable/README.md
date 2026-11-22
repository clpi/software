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
Obligations 10 to 13 and 15 to 20 are lane 2, closed in the
next section.

## Home record — lane 2 closure at its landing pin

Lane 2 closes obligations 10 to 13 and 15 to 20 in Second.lean
and Tests2.lean, on top of lane 1 at its pin. Closing pin: the
head commit of this repo at lane 2 landing, named in the lane
record (research folder, pareto lane 2 record of 2026-11-22).
Version tuple at the closing pin: table pin 9 (the test
instance); solver verdict version 1; checker reading version
1; instrument versions 1 on both test axes; Lean 4.19.0,
release commit 6caaee842e94. First-instance evidence tuple:
table pin ab4c9d4c7fcfff9156d4812450fdda4cfdb7d5fa18710efe8fee92563535cf94;
lane 5 checker version 1; lane 4 solver s1, checker c1;
instrument version 1 on all seven axes. Gate output at the
closing pin (cold): compile exit 0 over all four sources,
zero placeholders, 67 theorems axiom-audited, every one
depending on no axioms or on a subset of the standard three,
the hypothesis, naming, and premise audits passing over all
four sources, and the finiteness control refused as required.

The assembled optimality claim, at exactly its proved
strength (thirteen.optimal): for a space and its pinned table
where obligation 1's checker pass holds, and for every row of
the table — (1) the row is in the computed frontier if and
only if no row of the table dominates it; (2) if the row is
not in the computed frontier, some member of the computed
frontier dominates it; (3) the checker frontier and the
solver frontier have exactly the same members; and (4) no
row of the table dominates any member of the computed
frontier. That is the claim of section 1.1 of the methodology
record for the declared space at the pin, and nothing
stronger is claimed.

| Obligation | Theorem | Evidence beyond the proof |
|---|---|---|
| 10 soundness | ten.sound, from core.frontiff | proved from obligation 9's pairwise verdicts over the whole space as enumerated by obligation 1 |
| 11 completeness | eleven.complete, eleven.closed | the dominator produced is a frontier member; termination rests on core.countlt: the dominator count, counted from the finite row list, strictly falls along a dominance step, using obligation 3's derived finiteness and D5 strictness (no dominator dominates itself) |
| 12 checker identity | twelve.equal | the checker frontier is built from the cross reading alone; executed instance comparison: checks.checker on the test instance, and lane 5's executed comparison at the first instance pin (checker frontier of nine equals the solver and printed frontier; re-run at lane 2 closing, agreement true) |
| 13 assembled | thirteen.optimal | assembly from obligations 10, 11, 12 with no additional hypothesis; premises exactly P1 to P4 as inherited in content from the parts |
| 15 frontier cones | fifteen.scope, fifteen.kept | first-instance control, lane 4, re-run at lane 2 closing: one row change re-derived exactly the 34 cone-named pair verdicts and all 18 frontier verdicts, 272 pair verdicts carried, matching from-scratch; instance control checks.touch |
| 16 reuse on certificate | sixteen.member, sixteen.carry, sixteen.refusal | both controls, lane 4, re-run at lane 2 closing: an unchanged cone carries at zero re-derivation; a cone with exactly one changed cell refuses the carry and names the cell (the Seed item's power axis); instance control checks.carry |
| 17 incremental equals full | seventeen.equal, by induction over the operation sequence (seventeen.joinstep, seventeen.dropstep) | agreement evidence: lane 4's 24 per-operation equality receipts (re-run at lane 2 closing, all equal) and lane 5's 18 of 18 join replay; instance control checks.walk |
| 18 version binding | eighteen.binding, eighteen.changed | control checks.tuple: a verdict re-presented with exactly one tuple component changed, each of the four in turn, is not accepted |
| 19 premise registry | the premise audit in audit.py, run by the gate over all four sources | the audit enumerates every assumption of every closed proof of lanes 1 and 2 (108 assumption atoms at the closing pin) and matches each against the registry classes exactly: P1 and its stamped record as named premises; P2, P3, P4 in content as concrete pin equalities, the tally checker pass, and the separate checker code path; the remaining atoms are concrete decidable conditions, earlier obligations' conclusions, or the section 5 operation condition. No assumption outside the registry was found, so no obligation reopens on audit grounds. The audit refuses the controls draft and any signature carrying an unregistered assumption shape |
| 20 reopening scoped | twenty.scope, twenty.keptiff, twenty.partition | control checks.reopen on the instance's verdict table, and the first-instance form of the same control in lane 4's re-run gate: the row change reopened exactly the cone-named verdicts (34 pair, 18 frontier) and carried the other 272 |
