# What the theorems on master do not prove

A claim here is exactly what is proven at its pin. The audit findings F1 to F5 were
written against `de1b307` on `cursor/incremental-safety-0f5e`. That branch is on
master (PR 1, merge `642fd72`), and master has since added theorems that answer part
of each finding. This file says, per finding, what master proves and what it still
does not. The README table marks F1, F2, F4 and F5 "proven"; read each of those rows
together with the matching section below.

`gate/check.sh` shows the kernel accepts every proof with only `propext`,
`Quot.sound` and `Classical.choice`. It does not show that a statement means what
its name says. That is what this file is for.

## F1. Safety is checked on a submitted trace, not on the release's executions

Proven: order-sensitive, prefix-closed trace predicates are expressible
(`door_is_prefixClosed`, `f1_releaseSafe_distinguishes`, `c5_swap_does_not_yield_releaseSafe`).
In `OrderedIncrement`, rechecking the cone is equivalent to rechecking the whole
release for `TraceSafe` over abstract behaviors, given `Local`
(`ordered_incremental_iff_scratch`, `ordered_safety_preserved`).

Not proven: that the executable checker's verdict is about the executions of the
release. `ReleaseSafe` takes `traces` as a parameter. `check` and `f4_checker_sound`
use `[p.trace]`, one trace supplied with the patch. Nothing derives traces from code.
Standing control: `SubmittedTraceSys.trace_flips_verdict` (same release, the
submitted trace alone flips accept to refuse).

## F2. Noninterference is checked on a submitted one-bit system

Proven: the two-run condition `gm sys` separates a leaking from a non-leaking
one-bit function (`f2_two_run`), and profile-based checks cannot see the difference
(`same_profile`, `outputPoint_eq_iff`). In `OrderedIncrement`, `NI` is preserved by a
cone recheck given `Local` and a flow spec (`noninterference_preserved`), and
refinement alone does not preserve `NI` (`refinement_does_not_preserve_NI`).

Not proven: noninterference of the release's code. `Patch.sys : Bool → Bool` is
supplied with the patch and `releaseOf` ignores it. Standing controls:
`SubmittedTraceSys.sys_flips_verdict` and `SubmittedTraceSys.accept_not_release_function`
(every accepted patch has a twin with the same release that is refused).
`check_submitter_invariant` covers `deps`, `symHigh`, `obsHigh` and the budgets, not
`trace` or `sys`. Timing channels and implicit flows are outside the model.

## F3. Every preservation theorem rests on a complete dependency relation

Unchanged. `ClosureHyp`, `Local` and `SpecAuthority.calls` are premises, stated as
such (`f3_external_uses_closureHyp`). `coneExec_complete` and `coneExec_iff_affected`
show the computed cone covers the inductive cone over the given `calls` list. They
say nothing about dependencies the list leaves out: data, configuration, shared
state, timing, hardware, rollout. A change that reaches behavior through any of
those is outside the cone, and the theorems do not apply to it.

## F4. The checker is connected to a one-symbol release, and trust moved to the spec

Proven: `check ... = .accept → ReleaseSafe ... ∧ TaintFree ...` (`f4_checker_sound`,
`incremental_release_safe`), and the submitter's `deps`, labels and budgets do not
change the verdict (`check_submitter_invariant`, `c1_*`, `c2_*`, `c3_*`).

Not proven:
- Anything about the whole release after the change. The conclusion is about
  `releaseOf p`, which has exactly one symbol (`SubmittedTraceSys.releaseOf_one_symbol`).
  `coneViolator` inspects other roster symbols, but no conclusion mentions them.
- That the spec is right. `SpecAuthority` (allow and label maps, `calls`, `roster`,
  `forbidden`, bounds, `obsCost`) is trusted. C1 to C3 moved trust from the submitter
  to the spec writer and to the patch's `trace` and `sys`; it did not remove it.
- A link from this checker to `OrderedIncrement`. `f4_checker_sound` concludes the
  `Model.lean` `ReleaseSafe`, not `ReleaseGood` or `ConeGood`. `Family.Checker.incrCheck_sound`
  links a different executable checker to `recheck_iff_scratch`, under a supplied `Local`.
- Time or compute. `changedCost` sums the spec's `obsCost` over the patch's
  behaviors, and the same number is compared to both `boundTime` and `boundCompute`
  (`accept_cost_noWorse`). Nothing is measured.

## F5. Keeping qualified labels is not doing the job

Proven: a release that drops every behavior, or keeps a symbol with no behaviors, is
not `ReleaseSafe` when the prior qualification is non-empty (`nothing_refused`,
`empty_behaviors_refused`, `c4_abstract`), because `ReleaseSafe` requires every
previously qualified behavior label to remain.

Not proven: that the release still does its job. Behaviors are `Nat` labels.
Keeping a label is not performing the function, and nothing models liveness or
availability over executions.

## Outside this pass

- `Family`, `RenameReorder` and `NatRepr` passed the gate (kernel, axioms, escape scan).
  Their statements were not re-audited for meaning in this pass.
- The axiom walk follows dependencies transitively, so a `sorry` or extra axiom in a
  pinned sibling (composable `dce6564b`, optimality `16a6c690`, quantifiable `f3709926`)
  that any declaration here uses would fail the gate. The siblings' other files are
  not checked here.
- `idol/full-snapshot-admission-audit` (`11278f9`: `c53eafe` full-snapshot bridge and
  PR 9's ordered-trace and run-admission work) forked from this line at `4a17787` and
  is not on master. Nothing here depends on it.
