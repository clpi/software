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

def bare : SymbolProfile :=
  { id := 0, behaviors := [1], costs := [{ lo := 0, hi := 1 }] }

def bareOld : Release := { symbols := [bare] }

def bareNew : Release := bareOld

theorem not_bare_releaseAdmitted_acceptsRelease :
    bareOld.symbols = [bare] ∧
      bareNew.symbols = [bare] ∧
      bare.id = bare.id ∧
      (∀ b ∈ bare.costs, b.lo ≤ b.hi) ∧
      (∀ b ∈ bare.costs, b.lo ≤ b.hi) ∧
      bare.costs.length = bare.costs.length ∧
      (∀ x ∈ bare.costs.zip bare.costs, x.2.hi ≤ x.1.hi) ∧
      ((() : Unit) = ()) ∧
      ¬ SoftwareIsQuantifiable.Pareto.noWorse (1, 0) (0, 0) ∧
      ReleaseAdmitted bareOld bareNew ∧
      SoftwareIsQuantifiable.Pareto.acceptsRelease () ()
        (priorOf bare) (submissionOf bare) (0, 0) (1, 0) = false ∧
      ¬ (ReleaseAdmitted bareOld bareNew ↔
          SoftwareIsQuantifiable.Pareto.acceptsRelease () ()
            (priorOf bare) (submissionOf bare) (0, 0) (1, 0) = true) := by
  have hAdm : ReleaseAdmitted bareOld bareNew := (releaseAdmitted_iff).mp (by decide)
  have hAcc : SoftwareIsQuantifiable.Pareto.acceptsRelease () ()
      (priorOf bare) (submissionOf bare) (0, 0) (1, 0) = false := by decide
  refine ⟨rfl, rfl, rfl, ?_, ?_, rfl, ?_, rfl, by decide, hAdm, hAcc, ?_⟩
  · intro b hb
    simp [bare] at hb
    subst hb
    decide
  · intro b hb
    simp [bare] at hb
    subst hb
    decide
  · intro x hx
    simp [bare] at hx
    subst hx
    decide
  · intro hiff
    exact Bool.noConfusion ((hiff.mp hAdm).symm.trans hAcc)

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
    symR.symbols = [sym] ∧
      symR.symbols = [sym] ∧
      sym.id = sym.id ∧
      (∀ b ∈ sym.costs, b.lo ≤ b.hi) ∧
      (∀ b ∈ sym.costs, b.lo ≤ b.hi) ∧
      sym.costs.length = sym.costs.length ∧
      (∀ x ∈ sym.costs.zip sym.costs, x.2.hi ≤ x.1.hi) ∧
      ¬ ((1 : Nat) = 0) ∧
      SoftwareIsQuantifiable.Pareto.noWorse (2, 2) (2, 2) ∧
      ReleaseAdmitted symR symR ∧
      SoftwareIsQuantifiable.Pareto.acceptsRelease (0 : Nat) (1 : Nat)
        (priorOf sym) (submissionOf sym) (2, 2) (2, 2) = false ∧
      ¬ (ReleaseAdmitted symR symR ↔
          SoftwareIsQuantifiable.Pareto.acceptsRelease (0 : Nat) (1 : Nat)
            (priorOf sym) (submissionOf sym) (2, 2) (2, 2) = true) := by
  have hAdm : ReleaseAdmitted symR symR := (releaseAdmitted_iff).mp (by decide)
  have hAcc : SoftwareIsQuantifiable.Pareto.acceptsRelease (0 : Nat) (1 : Nat)
      (priorOf sym) (submissionOf sym) (2, 2) (2, 2) = false := by decide
  refine ⟨rfl, rfl, rfl, ?_, ?_, rfl, ?_, by decide, by decide, hAdm, hAcc, ?_⟩
  · intro b hb
    simp [sym] at hb
    subst hb
    decide
  · intro b hb
    simp [sym] at hb
    subst hb
    decide
  · intro x hx
    simp [sym] at hx
    subst hx
    decide
  · intro hiff
    exact Bool.noConfusion ((hiff.mp hAdm).symm.trans hAcc)

theorem not_upper :
    symR.symbols = [sym] ∧
      raisedR.symbols = [raised] ∧
      sym.id = raised.id ∧
      (∀ b ∈ sym.costs, b.lo ≤ b.hi) ∧
      (∀ b ∈ raised.costs, b.lo ≤ b.hi) ∧
      sym.costs.length = raised.costs.length ∧
      ¬ (∀ x ∈ sym.costs.zip raised.costs, x.2.hi ≤ x.1.hi) ∧
      ((() : Unit) = ()) ∧
      SoftwareIsQuantifiable.Pareto.noWorse (2, 2) (2, 2) ∧
      ¬ ReleaseAdmitted symR raisedR ∧
      SoftwareIsQuantifiable.Pareto.acceptsRelease () ()
        (priorOf sym) (submissionOf raised) (2, 2) (2, 2) = true ∧
      ¬ (ReleaseAdmitted symR raisedR ↔
          SoftwareIsQuantifiable.Pareto.acceptsRelease () ()
            (priorOf sym) (submissionOf raised) (2, 2) (2, 2) = true) := by
  have hAdm : ¬ ReleaseAdmitted symR raisedR := refused (by decide)
  have hAcc : SoftwareIsQuantifiable.Pareto.acceptsRelease () ()
      (priorOf sym) (submissionOf raised) (2, 2) (2, 2) = true := by decide
  refine ⟨rfl, rfl, rfl, ?_, ?_, rfl, ?_, rfl, by decide, hAdm, hAcc, ?_⟩
  · intro b hb
    simp [sym] at hb
    subst hb
    decide
  · intro b hb
    simp [raised] at hb
    subst hb
    decide
  · intro h
    have hle : (9 : Nat) ≤ 2 := h ({ lo := 0, hi := 2 }, { lo := 0, hi := 9 })
      (by simp [sym, raised])
    omega
  · intro hiff
    exact hAdm (hiff.mpr hAcc)

theorem not_point :
    symR.symbols = [sym] ∧
      symR.symbols = [sym] ∧
      sym.id = sym.id ∧
      (∀ b ∈ sym.costs, b.lo ≤ b.hi) ∧
      (∀ b ∈ sym.costs, b.lo ≤ b.hi) ∧
      sym.costs.length = sym.costs.length ∧
      (∀ x ∈ sym.costs.zip sym.costs, x.2.hi ≤ x.1.hi) ∧
      ((() : Unit) = ()) ∧
      ¬ SoftwareIsQuantifiable.Pareto.noWorse (1, 0) (0, 0) ∧
      ReleaseAdmitted symR symR ∧
      SoftwareIsQuantifiable.Pareto.acceptsRelease () ()
        (priorOf sym) (submissionOf sym) (0, 0) (1, 0) = false ∧
      ¬ (ReleaseAdmitted symR symR ↔
          SoftwareIsQuantifiable.Pareto.acceptsRelease () ()
            (priorOf sym) (submissionOf sym) (0, 0) (1, 0) = true) := by
  have hAdm : ReleaseAdmitted symR symR := (releaseAdmitted_iff).mp (by decide)
  have hAcc : SoftwareIsQuantifiable.Pareto.acceptsRelease () ()
      (priorOf sym) (submissionOf sym) (0, 0) (1, 0) = false := by decide
  refine ⟨rfl, rfl, rfl, ?_, ?_, rfl, ?_, rfl, by decide, hAdm, hAcc, ?_⟩
  · intro b hb
    simp [sym] at hb
    subst hb
    decide
  · intro b hb
    simp [sym] at hb
    subst hb
    decide
  · intro x hx
    simp [sym] at hx
    subst hx
    decide
  · intro hiff
    exact Bool.noConfusion ((hiff.mp hAdm).symm.trans hAcc)

theorem not_id :
    symR.symbols = [sym] ∧
      shiftedR.symbols = [shifted] ∧
      ¬ (sym.id = shifted.id) ∧
      (∀ b ∈ sym.costs, b.lo ≤ b.hi) ∧
      (∀ b ∈ shifted.costs, b.lo ≤ b.hi) ∧
      sym.costs.length = shifted.costs.length ∧
      (∀ x ∈ sym.costs.zip shifted.costs, x.2.hi ≤ x.1.hi) ∧
      ((() : Unit) = ()) ∧
      SoftwareIsQuantifiable.Pareto.noWorse (2, 2) (2, 2) ∧
      ¬ ReleaseAdmitted symR shiftedR ∧
      SoftwareIsQuantifiable.Pareto.acceptsRelease () ()
        (priorOf sym) (submissionOf shifted) (2, 2) (2, 2) = true ∧
      ¬ (ReleaseAdmitted symR shiftedR ↔
          SoftwareIsQuantifiable.Pareto.acceptsRelease () ()
            (priorOf sym) (submissionOf shifted) (2, 2) (2, 2) = true) := by
  have hAdm : ¬ ReleaseAdmitted symR shiftedR := refused (by decide)
  have hAcc : SoftwareIsQuantifiable.Pareto.acceptsRelease () ()
      (priorOf sym) (submissionOf shifted) (2, 2) (2, 2) = true := by decide
  refine ⟨rfl, rfl, by decide, ?_, ?_, rfl, ?_, rfl, by decide, hAdm, hAcc, ?_⟩
  · intro b hb
    simp [sym] at hb
    subst hb
    decide
  · intro b hb
    simp [shifted] at hb
    subst hb
    decide
  · intro x hx
    simp [sym, shifted] at hx
    subst hx
    decide
  · intro hiff
    exact hAdm (hiff.mpr hAcc)

theorem not_old_bounds :
    invertedR.symbols = [inverted] ∧
      lowHiR.symbols = [lowHi] ∧
      inverted.id = lowHi.id ∧
      ¬ (∀ b ∈ inverted.costs, b.lo ≤ b.hi) ∧
      (∀ b ∈ lowHi.costs, b.lo ≤ b.hi) ∧
      inverted.costs.length = lowHi.costs.length ∧
      (∀ x ∈ inverted.costs.zip lowHi.costs, x.2.hi ≤ x.1.hi) ∧
      ((() : Unit) = ()) ∧
      SoftwareIsQuantifiable.Pareto.noWorse (1, 1) (1, 1) ∧
      ¬ ReleaseAdmitted invertedR lowHiR ∧
      SoftwareIsQuantifiable.Pareto.acceptsRelease () ()
        (priorOf inverted) (submissionOf lowHi) (1, 1) (1, 1) = true ∧
      ¬ (ReleaseAdmitted invertedR lowHiR ↔
          SoftwareIsQuantifiable.Pareto.acceptsRelease () ()
            (priorOf inverted) (submissionOf lowHi) (1, 1) (1, 1) = true) := by
  have hAdm : ¬ ReleaseAdmitted invertedR lowHiR := refused (by decide)
  have hAcc : SoftwareIsQuantifiable.Pareto.acceptsRelease () ()
      (priorOf inverted) (submissionOf lowHi) (1, 1) (1, 1) = true := by decide
  refine ⟨rfl, rfl, rfl, ?_, ?_, rfl, ?_, rfl, by decide, hAdm, hAcc, ?_⟩
  · intro h
    have hle : (5 : Nat) ≤ 1 := h { lo := 5, hi := 1 } (by simp [inverted])
    omega
  · intro b hb
    simp [lowHi] at hb
    subst hb
    decide
  · intro x hx
    simp [inverted, lowHi] at hx
    subst hx
    decide
  · intro hiff
    exact hAdm (hiff.mpr hAcc)

theorem not_new_bounds :
    symR.symbols = [sym] ∧
      invertedR.symbols = [inverted] ∧
      sym.id = inverted.id ∧
      (∀ b ∈ sym.costs, b.lo ≤ b.hi) ∧
      ¬ (∀ b ∈ inverted.costs, b.lo ≤ b.hi) ∧
      sym.costs.length = inverted.costs.length ∧
      (∀ x ∈ sym.costs.zip inverted.costs, x.2.hi ≤ x.1.hi) ∧
      ((() : Unit) = ()) ∧
      SoftwareIsQuantifiable.Pareto.noWorse (1, 1) (1, 1) ∧
      ¬ ReleaseAdmitted symR invertedR ∧
      SoftwareIsQuantifiable.Pareto.acceptsRelease () ()
        (priorOf sym) (submissionOf inverted) (1, 1) (1, 1) = true ∧
      ¬ (ReleaseAdmitted symR invertedR ↔
          SoftwareIsQuantifiable.Pareto.acceptsRelease () ()
            (priorOf sym) (submissionOf inverted) (1, 1) (1, 1) = true) := by
  have hAdm : ¬ ReleaseAdmitted symR invertedR := refused (by decide)
  have hAcc : SoftwareIsQuantifiable.Pareto.acceptsRelease () ()
      (priorOf sym) (submissionOf inverted) (1, 1) (1, 1) = true := by decide
  refine ⟨rfl, rfl, rfl, ?_, ?_, rfl, ?_, rfl, by decide, hAdm, hAcc, ?_⟩
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
  · intro hiff
    exact hAdm (hiff.mpr hAcc)

theorem not_length :
    symR.symbols = [sym] ∧
      longerR.symbols = [longer] ∧
      sym.id = longer.id ∧
      (∀ b ∈ sym.costs, b.lo ≤ b.hi) ∧
      (∀ b ∈ longer.costs, b.lo ≤ b.hi) ∧
      ¬ (sym.costs.length = longer.costs.length) ∧
      (∀ x ∈ sym.costs.zip longer.costs, x.2.hi ≤ x.1.hi) ∧
      ((() : Unit) = ()) ∧
      SoftwareIsQuantifiable.Pareto.noWorse (2, 2) (2, 2) ∧
      ¬ ReleaseAdmitted symR longerR ∧
      SoftwareIsQuantifiable.Pareto.acceptsRelease () ()
        (priorOf sym) (submissionOf longer) (2, 2) (2, 2) = true ∧
      ¬ (ReleaseAdmitted symR longerR ↔
          SoftwareIsQuantifiable.Pareto.acceptsRelease () ()
            (priorOf sym) (submissionOf longer) (2, 2) (2, 2) = true) := by
  have hAdm : ¬ ReleaseAdmitted symR longerR := refused (by decide)
  have hAcc : SoftwareIsQuantifiable.Pareto.acceptsRelease () ()
      (priorOf sym) (submissionOf longer) (2, 2) (2, 2) = true := by decide
  refine ⟨rfl, rfl, rfl, ?_, ?_, by decide, ?_, rfl, by decide, hAdm, hAcc, ?_⟩
  · intro b hb
    simp [sym] at hb
    subst hb
    decide
  · intro b hb
    simp [longer] at hb
    subst hb
    decide
  · intro x hx
    simp [sym, longer] at hx
    subst hx
    decide
  · intro hiff
    exact hAdm (hiff.mpr hAcc)

theorem not_old_list :
    ¬ (twoOld.symbols = [sym]) ∧
      symR.symbols = [sym] ∧
      sym.id = sym.id ∧
      (∀ b ∈ sym.costs, b.lo ≤ b.hi) ∧
      (∀ b ∈ sym.costs, b.lo ≤ b.hi) ∧
      sym.costs.length = sym.costs.length ∧
      (∀ x ∈ sym.costs.zip sym.costs, x.2.hi ≤ x.1.hi) ∧
      ((() : Unit) = ()) ∧
      SoftwareIsQuantifiable.Pareto.noWorse (2, 2) (2, 2) ∧
      ¬ ReleaseAdmitted twoOld symR ∧
      SoftwareIsQuantifiable.Pareto.acceptsRelease () ()
        (priorOf sym) (submissionOf sym) (2, 2) (2, 2) = true ∧
      ¬ (ReleaseAdmitted twoOld symR ↔
          SoftwareIsQuantifiable.Pareto.acceptsRelease () ()
            (priorOf sym) (submissionOf sym) (2, 2) (2, 2) = true) := by
  have hAdm : ¬ ReleaseAdmitted twoOld symR := refused (by decide)
  have hAcc : SoftwareIsQuantifiable.Pareto.acceptsRelease () ()
      (priorOf sym) (submissionOf sym) (2, 2) (2, 2) = true := by decide
  refine ⟨by decide, rfl, rfl, ?_, ?_, rfl, ?_, rfl, by decide, hAdm, hAcc, ?_⟩
  · intro b hb
    simp [sym] at hb
    subst hb
    decide
  · intro b hb
    simp [sym] at hb
    subst hb
    decide
  · intro x hx
    simp [sym] at hx
    subst hx
    decide
  · intro hiff
    exact hAdm (hiff.mpr hAcc)

theorem not_new_list :
    symR.symbols = [sym] ∧
      ¬ (hiddenR.symbols = [sym]) ∧
      sym.id = sym.id ∧
      (∀ b ∈ sym.costs, b.lo ≤ b.hi) ∧
      (∀ b ∈ sym.costs, b.lo ≤ b.hi) ∧
      sym.costs.length = sym.costs.length ∧
      (∀ x ∈ sym.costs.zip sym.costs, x.2.hi ≤ x.1.hi) ∧
      ((() : Unit) = ()) ∧
      SoftwareIsQuantifiable.Pareto.noWorse (2, 2) (2, 2) ∧
      ¬ ReleaseAdmitted symR hiddenR ∧
      SoftwareIsQuantifiable.Pareto.acceptsRelease () ()
        (priorOf sym) (submissionOf sym) (2, 2) (2, 2) = true ∧
      ¬ (ReleaseAdmitted symR hiddenR ↔
          SoftwareIsQuantifiable.Pareto.acceptsRelease () ()
            (priorOf sym) (submissionOf sym) (2, 2) (2, 2) = true) := by
  have hAdm : ¬ ReleaseAdmitted symR hiddenR := refused (by decide)
  have hAcc : SoftwareIsQuantifiable.Pareto.acceptsRelease () ()
      (priorOf sym) (submissionOf sym) (2, 2) (2, 2) = true := by decide
  refine ⟨rfl, by decide, rfl, ?_, ?_, rfl, ?_, rfl, by decide, hAdm, hAcc, ?_⟩
  · intro b hb
    simp [sym] at hb
    subst hb
    decide
  · intro b hb
    simp [sym] at hb
    subst hb
    decide
  · intro x hx
    simp [sym] at hx
    subst hx
    decide
  · intro hiff
    exact hAdm (hiff.mpr hAcc)

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
