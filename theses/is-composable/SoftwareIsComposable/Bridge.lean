import SoftwareIsComposable.Admission
import SoftwareIsQuantifiable.Interface
import SoftwareIsQuantifiable.Pareto

namespace SoftwareIsComposable

def priorOf (p : SymbolProfile) : SoftwareIsQuantifiable.Pareto.PriorQualification Nat :=
  { qualified := p.behaviors }

def submissionOf (p : SymbolProfile) :
    SoftwareIsQuantifiable.Pareto.BehaviorSubmission Nat :=
  { offered := p.behaviors }

def admittedBySpec {B Context : Type} [DecidableEq B] [DecidableEq Context]
    (baselineContext candidateContext : Context)
    (prior : SoftwareIsQuantifiable.Pareto.PriorQualification B)
    (submission : SoftwareIsQuantifiable.Pareto.BehaviorSubmission B)
    (inc out : SoftwareIsQuantifiable.Pareto.Point) : Prop :=
  prior.qualified ≠ [] ∧
    SoftwareIsQuantifiable.Pareto.acceptsRelease baselineContext candidateContext
      prior submission inc out = true

theorem releaseAdmitted_iff_acceptsRelease
    {Context : Type} [DecidableEq Context]
    {old new : SymbolProfile} {oldR newR : Release}
    {baselineContext candidateContext : Context}
    {inc out : SoftwareIsQuantifiable.Pareto.Point}
    (hOld : oldR.symbols = [old])
    (hNew : newR.symbols = [new])
    (hId : old.id = new.id)
    (hValidOld : ∀ b ∈ old.costs, b.lo ≤ b.hi)
    (hValidNew : ∀ b ∈ new.costs, b.lo ≤ b.hi)
    (hLen : old.costs.length = new.costs.length)
    (hHi : ∀ x ∈ old.costs.zip new.costs, x.2.hi ≤ x.1.hi)
    (hCtx : candidateContext = baselineContext)
    (hPoint : SoftwareIsQuantifiable.Pareto.noWorse out inc) :
    ReleaseAdmitted oldR newR ↔
      SoftwareIsQuantifiable.Pareto.acceptsRelease baselineContext candidateContext
        (priorOf old) (submissionOf new) inc out = true := by
  constructor
  · intro hR
    have hmem : old ∈ oldR.symbols := by simp [hOld]
    have hadm := hR old hmem
    have hfind : newR.symbols.find? (fun q => q.id == old.id) = some new := by
      simp [hNew, hId, beq_iff_eq]
    simp [hfind] at hadm
    exact (SoftwareIsQuantifiable.Pareto.acceptsRelease_iff baselineContext
      candidateContext (priorOf old) (submissionOf new) inc out).mpr
      ⟨hCtx, fun b hb => hadm.keeps b (by simpa [priorOf] using hb), hPoint⟩
  · intro hAcc
    intro p hp
    have hp' : p = old := List.mem_singleton.mp (by simpa [hOld] using hp)
    subst hp'
    have hiff := (SoftwareIsQuantifiable.Pareto.acceptsRelease_iff baselineContext
      candidateContext (priorOf old) (submissionOf new) inc out).mp hAcc
    have hfind : newR.symbols.find? (fun q => q.id == old.id) = some new := by
      simp [hNew, hId, beq_iff_eq]
    simp [hfind]
    exact ⟨hId, hValidOld, hValidNew, fun b hb => hiff.2.1 b (by simpa [priorOf] using hb),
      hLen, hHi⟩

def bareOld : Release :=
  { symbols := [{ id := 0, behaviors := [1], costs := [{ lo := 0, hi := 1 }] }] }

def bareNew : Release := bareOld

theorem not_bare_releaseAdmitted_acceptsRelease :
    ReleaseAdmitted bareOld bareNew ∧
      SoftwareIsQuantifiable.Pareto.acceptsRelease () ()
        (priorOf { id := 0, behaviors := [1], costs := [{ lo := 0, hi := 1 }] })
        (submissionOf { id := 0, behaviors := [1], costs := [{ lo := 0, hi := 1 }] })
        (0, 0) (1, 0) = false := by
  constructor
  · exact (releaseAdmitted_iff (old := bareOld) (new := bareNew)).mp (by decide)
  · decide

theorem nothing_below
    (space : SoftwareIsQuantifiable.Interface.MeasureSpace Unit)
    (inc : SoftwareIsQuantifiable.Pareto.Point) :
    SoftwareIsQuantifiable.Interface.releaseLe space
        ([] : SoftwareIsQuantifiable.Interface.Release Unit Unit)
        ([] : SoftwareIsQuantifiable.Interface.Release Unit Unit) ∧
      ∀ prior : SoftwareIsQuantifiable.Pareto.PriorQualification Nat,
        ¬ admittedBySpec () () prior { offered := [] } inc inc := by
  refine ⟨?_, ?_⟩
  · exact SoftwareIsQuantifiable.Interface.releaseLe_refl
      (by simp [SoftwareIsQuantifiable.Interface.uniqueSymbols])
      (fun _ hp => nomatch hp)
  · intro prior hbad
    rcases hbad with ⟨hne, hacc⟩
    have hiff := (SoftwareIsQuantifiable.Pareto.acceptsRelease_iff () () prior
      { offered := [] } inc inc).mp hacc
    match hqual : prior.qualified with
    | [] => exact hne hqual
    | b :: _ => exact List.not_mem_nil b (hiff.2.1 b (by simp [hqual]))

end SoftwareIsComposable
