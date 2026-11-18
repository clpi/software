import SoftwareIsIncrementallySafe.Safety

namespace SoftwareIsIncrementallySafe

open SoftwareIsComposable
open SoftwareIsIncrementallyCertifiable
open Classical

def ClosureHyp {σ ω : Type} (deps : σ → σ → Prop) (d : Delta σ ω) : Prop :=
  ∀ s, Cone deps d.changed s → d.inspect s = true

def Within {σ ω : Type} (allow : σ → ω → Prop) (deps : σ → σ → Prop)
    (B : σ → Profile ω) : Prop :=
  ∀ s o, Reaches deps B s o → allow s o

def ReleaseSafe {σ ω : Type} (allow : σ → ω → Prop) (deps : σ → σ → Prop)
    (R : Release σ ω) : Prop :=
  Within allow deps R.behavior

def ConeAccept {σ ω : Type} (allow : σ → ω → Prop) (deps : σ → σ → Prop)
    (R : Release σ ω) (d : Delta σ ω) : Prop :=
  ∀ s, d.inspect s = true →
    ∀ o, Reaches deps (apply R d).behavior s o → allow s o

theorem incremental_iff_scratch {σ ω : Type}
    (allow : σ → ω → Prop) (deps : σ → σ → Prop)
    (R : Release σ ω) (d : Delta σ ω)
    (hR : ReleaseSafe allow deps R)
    (hClo : ClosureHyp deps d) :
    ConeAccept allow deps R d ↔ ReleaseSafe allow deps (apply R d) := by
  constructor
  · intro hAcc s o hr
    by_cases hc : Cone deps d.changed s
    · exact hAcc s (hClo s hc) o hr
    · exact hR s o ((reaches_outside_stable (fun t ht => apply_unchanged R d ht) hc).mp hr)
  · intro hSafe s _ o hr
    exact hSafe s o hr

theorem preserve_safety {σ ω : Type}
    (allow : σ → ω → Prop) (deps : σ → σ → Prop)
    (R : Release σ ω) (d : Delta σ ω)
    (hR : ReleaseSafe allow deps R)
    (hClo : ClosureHyp deps d)
    (hAcc : ConeAccept allow deps R d) :
    ReleaseSafe allow deps (apply R d) :=
  (incremental_iff_scratch allow deps R d hR hClo).mp hAcc

inductive Chain (σ ω : Type) where
  | base (R : Release σ ω)
  | step (prev : Chain σ ω) (d : Delta σ ω)

def Chain.final {σ ω : Type} : Chain σ ω → Release σ ω
  | .base R => R
  | .step prev d => apply prev.final d

def Chain.closureHyps {σ ω : Type} (deps : σ → σ → Prop) : Chain σ ω → Prop
  | .base _ => True
  | .step prev d => prev.closureHyps deps ∧ ClosureHyp deps d

def Chain.incrAccept {σ ω : Type} (allow : σ → ω → Prop) (deps : σ → σ → Prop) :
    Chain σ ω → Prop
  | .base R => ReleaseSafe allow deps R
  | .step prev d =>
      prev.incrAccept allow deps ∧ ClosureHyp deps d ∧
        ConeAccept allow deps prev.final d

def Chain.allScratch {σ ω : Type} (allow : σ → ω → Prop) (deps : σ → σ → Prop) :
    Chain σ ω → Prop
  | .base R => ReleaseSafe allow deps R
  | .step prev d =>
      prev.allScratch allow deps ∧ ReleaseSafe allow deps (apply prev.final d)

theorem allScratch_final {σ ω : Type}
    (allow : σ → ω → Prop) (deps : σ → σ → Prop)
    {c : Chain σ ω} (h : Chain.allScratch allow deps c) :
    ReleaseSafe allow deps c.final := by
  induction c with
  | base _ => exact h
  | step _ _ _ => exact h.2

theorem chain_incremental_iff_scratch {σ ω : Type}
    (allow : σ → ω → Prop) (deps : σ → σ → Prop) (c : Chain σ ω) :
    Chain.closureHyps deps c →
      (Chain.incrAccept allow deps c ↔ Chain.allScratch allow deps c) := by
  induction c with
  | base _ =>
    intro _
    exact Iff.rfl
  | step prev d ih =>
    intro hClo
    rcases hClo with ⟨hCloPrev, hCloStep⟩
    constructor
    · intro h
      rcases h with ⟨hprev, _, hAcc⟩
      have hprevS := (ih hCloPrev).mp hprev
      exact ⟨hprevS,
        (incremental_iff_scratch allow deps prev.final d
          (allScratch_final allow deps hprevS) hCloStep).mp hAcc⟩
    · intro h
      rcases h with ⟨hprevS, hfin⟩
      exact ⟨(ih hCloPrev).mpr hprevS, hCloStep,
        (incremental_iff_scratch allow deps prev.final d
          (allScratch_final allow deps hprevS) hCloStep).mpr hfin⟩

theorem chain_final_of_incremental {σ ω : Type}
    (allow : σ → ω → Prop) (deps : σ → σ → Prop)
    {c : Chain σ ω}
    (hClo : Chain.closureHyps deps c)
    (h : Chain.incrAccept allow deps c) :
    ReleaseSafe allow deps c.final :=
  allScratch_final allow deps ((chain_incremental_iff_scratch allow deps c hClo).mp h)

theorem composed_incremental_iff_final {σ ω : Type}
    (allow : σ → ω → Prop) (deps : σ → σ → Prop)
    (R : Release σ ω) (ds : List (Delta σ ω))
    (hR : ReleaseSafe allow deps R)
    (hClo : ClosureHyp deps (composeAll ds)) :
    ConeAccept allow deps R (composeAll ds) ↔
      ReleaseSafe allow deps (foldApply R ds) := by
  rw [foldApply_eq_composeAll]
  exact incremental_iff_scratch allow deps R (composeAll ds) hR hClo

end SoftwareIsIncrementallySafe
