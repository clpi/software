import SoftwareIsIncrementallySafe

/-!
Standing control: the checker's verdict is not a function of the release.

`check` reads `Patch.trace` and `Patch.sys`, both supplied with the change, and
`releaseOf` ignores both. So two patches with the same release can get different
verdicts. `check_submitter_invariant` covers `deps`, `symHigh`, `obsHigh` and the
budgets; it does not cover `trace` or `sys`. The trust that C1 to C3 removed from
the submitter still sits with whoever supplies `trace` and `sys`.

`f4_checker_sound` concludes `ReleaseSafe` of `releaseOf p`, a release with exactly
one symbol, over the one submitted trace and the submitted one-bit system.
-/

open SoftwareIsComposable
open SoftwareIsQuantifiable.Pareto

namespace SoftwareIsIncrementallySafe.SubmittedTraceSys

/-- Every accepted patch has a twin with the same release that is refused:
swap in a system that leaks its input bit. -/
theorem accept_not_release_function (spec : SpecAuthority) (prior : PriorQualification Nat)
    (p : Patch) (_h : check spec prior p = .accept) :
    releaseOf { p with sys := leakSys } = releaseOf p ∧
      check spec prior { p with sys := leakSys } ≠ .accept := by
  refine ⟨rfl, ?_⟩
  have hgm : gmB leakSys = false := by decide
  simp [check, symbolAdmitted, hgm]

/-- Same release, same trace, different submitted `sys`: accept and refuse. -/
theorem sys_flips_verdict :
    releaseOf (doorPatch ["stop", "open"] noiseSys) =
        releaseOf (doorPatch ["stop", "open"] leakSys) ∧
      check doorAuthority doorPrior (doorPatch ["stop", "open"] noiseSys) = .accept ∧
      check doorAuthority doorPrior (doorPatch ["stop", "open"] leakSys) = .refuse 50 := by
  refine ⟨rfl, ?_, ?_⟩ <;> decide

/-- Same release, same `sys`, different submitted trace: accept and refuse. -/
theorem trace_flips_verdict :
    releaseOf (doorPatch ["stop", "open"] noiseSys) =
        releaseOf (doorPatch ["open", "stop"] noiseSys) ∧
      check doorAuthority doorPrior (doorPatch ["stop", "open"] noiseSys) = .accept ∧
      check doorAuthority doorPrior (doorPatch ["open", "stop"] noiseSys) = .refuse 50 := by
  refine ⟨rfl, ?_, ?_⟩ <;> decide

/-- The release that `f4_checker_sound` speaks about has one symbol. -/
theorem releaseOf_one_symbol (p : Patch) : (releaseOf p).symbols.length = 1 := rfl

end SoftwareIsIncrementallySafe.SubmittedTraceSys

/--
info: 'SoftwareIsIncrementallySafe.SubmittedTraceSys.accept_not_release_function' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SoftwareIsIncrementallySafe.SubmittedTraceSys.accept_not_release_function

#print axioms SoftwareIsIncrementallySafe.SubmittedTraceSys.sys_flips_verdict
#print axioms SoftwareIsIncrementallySafe.SubmittedTraceSys.trace_flips_verdict
#print axioms SoftwareIsIncrementallySafe.SubmittedTraceSys.releaseOf_one_symbol
