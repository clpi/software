import Qualification
import SoftwareIsComposable.Incremental

namespace SoftwareDoesntNeedReview

namespace Narrow

structure ClosureHyp (calls : List (Nat × Nat)) (changed : List Nat) : Prop where
  cone : ∀ s, SoftwareIsComposable.InClosure calls changed s ↔
    HypergraphIncremental.Affected
      (SoftwareIsComposable.hyper [] calls)
      (SoftwareIsComposable.hyper changed calls) s

theorem closureHyp_of_affected (calls : List (Nat × Nat)) (changed : List Nat) :
    ClosureHyp calls changed where
  cone _ := SoftwareIsComposable.inClosure_iff_affected

structure UnchangedBasis {A : Type} (B B' : A → Prop)
    (R R' : List A → A → Prop) : Prop where
  roots : ∀ a, B a ↔ B' a
  rules : ∀ ps a, R ps a ↔ R' ps a

def recheck (calls : List (Nat × Nat)) (changed : List Nat)
    (old new : SoftwareIsComposable.Release) : Prop :=
  ∀ s, SoftwareIsComposable.InClosure calls changed s →
    SoftwareIsComposable.symbolChecked old new s

theorem narrow_recheck_iff
    {A : Type} {B B' : A → Prop} {R R' : List A → A → Prop}
    (basis : UnchangedBasis B B' R R')
    (calls : List (Nat × Nat)) (changed : List Nat)
    (H : ClosureHyp calls changed)
    (old new : SoftwareIsComposable.Release)
    (hvalid : ∀ p ∈ old.symbols, ∀ b ∈ p.costs, b.lo ≤ b.hi)
    (stable : ∀ p ∈ old.symbols,
      ¬ SoftwareIsComposable.InClosure calls changed p.id →
        new.symbols.find? (fun q => q.id == p.id) = some p) :
    (SoftwareIsComposable.ReleaseAdmitted old new ↔ recheck calls changed old new) ∧
      (∀ a, B a ↔ B' a) ∧ (∀ ps a, R ps a ↔ R' ps a) := by
  refine ⟨?_, basis.roots, basis.rules⟩
  have hstable :
      ∀ p ∈ old.symbols,
        ¬ HypergraphIncremental.Affected
            (SoftwareIsComposable.hyper [] calls)
            (SoftwareIsComposable.hyper changed calls) p.id →
          new.symbols.find? (fun q => q.id == p.id) = some p := by
    intro p hp hna
    exact stable p hp fun hin => hna ((H.cone p.id).mp hin)
  have hadm := SoftwareIsComposable.incrementalRecheck_iff (calls := calls)
    (changed := changed) (old := old) (new := new) hvalid hstable
  constructor
  · intro h s hs
    exact hadm.mp h s ((H.cone s).mp hs)
  · intro h
    apply hadm.mpr
    intro s ha
    exact h s ((H.cone s).mpr ha)

theorem narrow_rubber
    {A : Type} {B B' : A → Prop} {R R' : List A → A → Prop}
    (basis : UnchangedBasis B B' R R')
    (calls : List (Nat × Nat)) (changed : List Nat)
    (H : ClosureHyp calls changed)
    (old new : SoftwareIsComposable.Release)
    (hvalid : ∀ p ∈ old.symbols, ∀ b ∈ p.costs, b.lo ≤ b.hi)
    (stable : ∀ p ∈ old.symbols,
      ¬ SoftwareIsComposable.InClosure calls changed p.id →
        new.symbols.find? (fun q => q.id == p.id) = some p)
    (bit : Bool)
    (review : bit = true ↔ recheck calls changed old new) :
    bit = true ↔ SoftwareIsComposable.ReleaseAdmitted old new := by
  rw [review]
  exact (narrow_recheck_iff basis calls changed H old new hvalid stable).1.symm

theorem sound_needs_premises
    {A : Type} {B TrueAt : A → Prop} {R : List A → A → Prop} {a : A}
    (hder : Qualification.Derives B R a) (hnot : ¬ TrueAt a) :
    ¬ ((∀ x, B x → TrueAt x) ∧ Qualification.Closed R TrueAt) := by
  intro h
  exact hnot (Qualification.soundness h.1 h.2 a hder)

end Narrow

end SoftwareDoesntNeedReview
