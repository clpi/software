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

theorem oneSymbol
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
    have hpEq : p = old := List.mem_singleton.mp (by simpa [hOld] using hp)
    cases hpEq
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

def sym : SymbolProfile :=
  { id := 0, behaviors := [1], costs := [{ lo := 0, hi := 2 }] }

def symR : Release := { symbols := [sym] }

def raised : SymbolProfile :=
  { id := 0, behaviors := [1], costs := [{ lo := 0, hi := 9 }] }

def raisedR : Release := { symbols := [raised] }

def shifted : SymbolProfile :=
  { id := 1, behaviors := [1], costs := [{ lo := 0, hi := 2 }] }

def shiftedR : Release := { symbols := [shifted] }

def inverted : SymbolProfile :=
  { id := 0, behaviors := [1], costs := [{ lo := 5, hi := 1 }] }

def invertedR : Release := { symbols := [inverted] }

def lowHi : SymbolProfile :=
  { id := 0, behaviors := [1], costs := [{ lo := 0, hi := 1 }] }

def lowHiR : Release := { symbols := [lowHi] }

def longer : SymbolProfile :=
  { id := 0, behaviors := [1],
    costs := [{ lo := 0, hi := 2 }, { lo := 0, hi := 2 }] }

def longerR : Release := { symbols := [longer] }

def extra : SymbolProfile :=
  { id := 1, behaviors := [7], costs := [{ lo := 0, hi := 2 }] }

def twoOld : Release := { symbols := [sym, extra] }

def dropped : SymbolProfile :=
  { id := 0, behaviors := [], costs := [{ lo := 0, hi := 2 }] }

def hiddenR : Release := { symbols := [dropped, sym] }

theorem refused {old new : Release} (h : releaseAdmitted old new = false) :
    ¬ ReleaseAdmitted old new := by
  intro hadm
  exact Bool.noConfusion (((releaseAdmitted_iff).mpr hadm).symm.trans h)

theorem not_context :
    ¬ ((1 : Nat) = 0) ∧
      ReleaseAdmitted symR symR ∧
      SoftwareIsQuantifiable.Pareto.acceptsRelease (0 : Nat) (1 : Nat)
        (priorOf sym) (submissionOf sym) (2, 2) (2, 2) = false := by
  refine ⟨by decide, (releaseAdmitted_iff).mp (by decide), by decide⟩

theorem not_upper :
    ((sym.costs.zip raised.costs).any (fun x => decide (x.2.hi > x.1.hi))) = true ∧
      ¬ ReleaseAdmitted symR raisedR ∧
      SoftwareIsQuantifiable.Pareto.acceptsRelease () ()
        (priorOf sym) (submissionOf raised) (2, 2) (2, 2) = true := by
  refine ⟨by decide, refused (by decide), by decide⟩

theorem not_point :
    ¬ SoftwareIsQuantifiable.Pareto.noWorse (1, 0) (0, 0) ∧
      ReleaseAdmitted symR symR ∧
      SoftwareIsQuantifiable.Pareto.acceptsRelease () ()
        (priorOf sym) (submissionOf sym) (0, 0) (1, 0) = false := by
  refine ⟨by decide, (releaseAdmitted_iff).mp (by decide), by decide⟩

theorem not_id :
    sym.id ≠ shifted.id ∧
      ¬ ReleaseAdmitted symR shiftedR ∧
      SoftwareIsQuantifiable.Pareto.acceptsRelease () ()
        (priorOf sym) (submissionOf shifted) (2, 2) (2, 2) = true := by
  refine ⟨by decide, refused (by decide), by decide⟩

theorem not_old_bounds :
    ¬ (∀ b ∈ inverted.costs, b.lo ≤ b.hi) ∧
      (∀ x ∈ inverted.costs.zip lowHi.costs, x.2.hi ≤ x.1.hi) ∧
      ¬ ReleaseAdmitted invertedR lowHiR ∧
      SoftwareIsQuantifiable.Pareto.acceptsRelease () ()
        (priorOf inverted) (submissionOf lowHi) (1, 1) (1, 1) = true := by
  refine ⟨?_, ?_, refused (by decide), by decide⟩
  · intro h
    have hle : (5 : Nat) ≤ 1 := h { lo := 5, hi := 1 } (by simp [inverted])
    omega
  · intro x hx
    simp [inverted, lowHi] at hx
    subst hx
    decide

theorem not_new_bounds :
    (∀ b ∈ sym.costs, b.lo ≤ b.hi) ∧
      ¬ (∀ b ∈ inverted.costs, b.lo ≤ b.hi) ∧
      (∀ x ∈ sym.costs.zip inverted.costs, x.2.hi ≤ x.1.hi) ∧
      ¬ ReleaseAdmitted symR invertedR ∧
      SoftwareIsQuantifiable.Pareto.acceptsRelease () ()
        (priorOf sym) (submissionOf inverted) (1, 1) (1, 1) = true := by
  refine ⟨?_, ?_, ?_, refused (by decide), by decide⟩
  · intro b hb
    simp [sym] at hb
    subst hb
    decide
  · intro h
    have hle : (5 : Nat) ≤ 1 := h { lo := 5, hi := 1 } (by simp [inverted])
    omega
  · intro x hx
    simp [sym, inverted] at hx
    subst hx
    decide

theorem not_length :
    sym.costs.length ≠ longer.costs.length ∧
      (∀ x ∈ sym.costs.zip longer.costs, x.2.hi ≤ x.1.hi) ∧
      ¬ ReleaseAdmitted symR longerR ∧
      SoftwareIsQuantifiable.Pareto.acceptsRelease () ()
        (priorOf sym) (submissionOf longer) (2, 2) (2, 2) = true := by
  refine ⟨by decide, ?_, refused (by decide), by decide⟩
  intro x hx
  simp [sym, longer] at hx
  subst hx
  decide

theorem not_old_list :
    twoOld.symbols ≠ [sym] ∧
      symR.symbols = [sym] ∧
      ¬ ReleaseAdmitted twoOld symR ∧
      SoftwareIsQuantifiable.Pareto.acceptsRelease () ()
        (priorOf sym) (submissionOf sym) (2, 2) (2, 2) = true := by
  refine ⟨by decide, rfl, refused (by decide), by decide⟩

theorem not_new_list :
    hiddenR.symbols ≠ [sym] ∧
      symR.symbols = [sym] ∧
      ¬ ReleaseAdmitted symR hiddenR ∧
      SoftwareIsQuantifiable.Pareto.acceptsRelease () ()
        (priorOf sym) (submissionOf sym) (2, 2) (2, 2) = true := by
  refine ⟨by decide, rfl, refused (by decide), by decide⟩

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
    | b :: _ =>
      have hbq : b ∈ prior.qualified := by
        rw [hqual]
        exact List.mem_cons.mpr (Or.inl rfl)
      exact List.not_mem_nil (hiff.2.1 b hbq)

end SoftwareIsComposable
