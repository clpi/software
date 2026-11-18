import SoftwareIsQuantifiable.Interface

open SoftwareIsQuantifiable.Interface

namespace SoftwareIsIncrementallySafe
namespace RenameReorder

structure Renaming (Binder : Type) where
  fwd : Binder → Binder
  bwd : Binder → Binder
  bwd_fwd : ∀ b, bwd (fwd b) = b
  fwd_bwd : ∀ b, fwd (bwd b) = b

def WellFormed {Symbol Measure : Type} (space : MeasureSpace Measure)
    (R : Release Symbol Measure) : Prop :=
  uniqueSymbols R ∧ profilesAligned space R

def ZeroDelta {Symbol Measure : Type} (space : MeasureSpace Measure)
    (a b : Release Symbol Measure) : Prop :=
  releaseLe space a b ∧ releaseLe space b a ∧
    ¬ releaseDominates space a b ∧ ¬ releaseDominates space b a

def FrontierInvariant {Symbol Measure : Type} [DecidableEq Symbol]
    (space : MeasureSpace Measure) (a b : Release Symbol Measure) : Prop :=
  ∀ (field : List (Profile Symbol Measure)) (x : Profile Symbol Measure),
    x ∈ frontier space (field ++ a) ↔ x ∈ frontier space (field ++ b)

def DigestRenameInvariant {Prog Binder Digest : Type}
    (rename : Renaming Binder → Prog → Prog) (digest : Prog → Digest) : Prop :=
  ∀ σ p, digest (rename σ p) = digest p

def DigestCollisionFree {Prog Digest : Type}
    (equiv : Prog → Prog → Prop) (digest : Prog → Digest) : Prop :=
  ∀ p q, digest p = digest q → equiv p q

def ProfileRespects {Prog Symbol Measure : Type}
    (equiv : Prog → Prog → Prop) (profileOf : Prog → Release Symbol Measure) : Prop :=
  ∀ p q, equiv p q → profileOf p = profileOf q

def RenameConclusion {Prog Binder Symbol Measure : Type} [DecidableEq Symbol]
    (space : MeasureSpace Measure)
    (rename : Renaming Binder → Prog → Prog)
    (profileOf : Prog → Release Symbol Measure) : Prop :=
  ∀ σ p, WellFormed space (profileOf p) →
    profileOf (rename σ p) = profileOf p ∧
    ZeroDelta space (profileOf (rename σ p)) (profileOf p) ∧
    FrontierInvariant space (profileOf (rename σ p)) (profileOf p)

def RenameZeroDelta {Prog Binder Digest Symbol Measure : Type} [DecidableEq Symbol]
    (space : MeasureSpace Measure)
    (rename : Renaming Binder → Prog → Prog) (digest : Prog → Digest)
    (equiv : Prog → Prog → Prop) (profileOf : Prog → Release Symbol Measure) : Prop :=
  DigestRenameInvariant rename digest →
  DigestCollisionFree equiv digest →
  ProfileRespects equiv profileOf →
  RenameConclusion space rename profileOf

def EffectAlgebraSound {Effect Prog Symbol Measure : Type}
    (commutes : Effect → Effect → Prop) (ctx : Effect → Effect → Prog)
    (profileOf : Prog → Release Symbol Measure) : Prop :=
  ∀ e₁ e₂, commutes e₁ e₂ → profileOf (ctx e₁ e₂) = profileOf (ctx e₂ e₁)

def DigestOrderOnlyIfCommutes {Effect Prog Digest : Type}
    (commutes : Effect → Effect → Prop) (ctx : Effect → Effect → Prog)
    (digest : Prog → Digest) : Prop :=
  ∀ e₁ e₂, digest (ctx e₁ e₂) = digest (ctx e₂ e₁) → commutes e₁ e₂

def ReorderConclusion {Effect Prog Digest Symbol Measure : Type} [DecidableEq Symbol]
    (space : MeasureSpace Measure)
    (commutes : Effect → Effect → Prop) (ctx : Effect → Effect → Prog)
    (digest : Prog → Digest) (profileOf : Prog → Release Symbol Measure) : Prop :=
  ∀ e₁ e₂, WellFormed space (profileOf (ctx e₁ e₂)) →
    (commutes e₁ e₂ →
      ZeroDelta space (profileOf (ctx e₁ e₂)) (profileOf (ctx e₂ e₁)) ∧
      FrontierInvariant space (profileOf (ctx e₁ e₂)) (profileOf (ctx e₂ e₁))) ∧
    (digest (ctx e₁ e₂) = digest (ctx e₂ e₁) →
      ZeroDelta space (profileOf (ctx e₁ e₂)) (profileOf (ctx e₂ e₁)))

def CommutingReorderZeroDelta {Effect Prog Digest Symbol Measure : Type} [DecidableEq Symbol]
    (space : MeasureSpace Measure)
    (commutes : Effect → Effect → Prop) (ctx : Effect → Effect → Prog)
    (digest : Prog → Digest) (profileOf : Prog → Release Symbol Measure) : Prop :=
  EffectAlgebraSound commutes ctx profileOf →
  DigestOrderOnlyIfCommutes commutes ctx digest →
  ReorderConclusion space commutes ctx digest profileOf

def lastWrite (writes : List Nat) : Nat := writes.getLast?.getD 0

def cellSpace : MeasureSpace Unit := [{ measure := (), polarity := .minimize }]

def cellRelease (writes : List Nat) : Release Unit Unit :=
  [{ symbol := (), readings := [lastWrite writes], observed := true }]

def NonCommutingChangesProfile : Prop :=
  (cellRelease [1, 2]).map Profile.readings ≠ (cellRelease [2, 1]).map Profile.readings ∧
  ¬ releaseLe cellSpace (cellRelease [1, 2]) (cellRelease [2, 1]) ∧
  ∀ x ∈ cellRelease [1, 2], x ∉ frontier cellSpace (cellRelease [1, 2] ++ cellRelease [2, 1])

def UnorderedDigestUnsound : Prop :=
  [1, 2].sum = [2, 1].sum ∧
  (cellRelease [1, 2]).map Profile.readings ≠ (cellRelease [2, 1]).map Profile.readings

theorem unorderedDigestUnsound : UnorderedDigestUnsound := by
  unfold UnorderedDigestUnsound cellRelease lastWrite
  decide

theorem nonCommutingChangesProfile : NonCommutingChangesProfile := by
  refine ⟨by decide, ?_, ?_⟩
  · intro h
    obtain ⟨p, hp, hnw⟩ := h.2.2.2.2 _ List.mem_cons_self
    simp only [cellRelease, List.mem_singleton] at hp
    subst hp
    have hax := hnw.1.2
    simp [axesLe, axisLe, cellSpace, lastWrite] at hax
  · intro x hx h
    simp only [cellRelease, List.mem_singleton] at hx
    subst hx
    have hnd := (frontier_exact.mp h).2.2
    exact hnd _ (List.mem_append_right _ List.mem_cons_self) (by decide)

def negation : Renaming Bool where
  fwd := not
  bwd := not
  bwd_fwd := Bool.not_not
  fwd_bwd := Bool.not_not

def binderRename (σ : Renaming Bool) (b : Bool) : Bool := σ.fwd b

def binderRelease (b : Bool) : Release Unit Unit :=
  [{ symbol := (), readings := [if b then 1 else 0], observed := true }]

def writePair (e₁ e₂ : Nat) : List Nat := [e₁, e₂]

def RenameNeedsDigestRenameInvariant : Prop :=
  DigestCollisionFree (@Eq Bool) id ∧
  ProfileRespects (@Eq Bool) binderRelease ∧
  ¬ RenameConclusion cellSpace binderRename binderRelease

def RenameNeedsDigestCollisionFree : Prop :=
  DigestRenameInvariant binderRename (fun _ : Bool => ()) ∧
  ProfileRespects (@Eq Bool) binderRelease ∧
  ¬ RenameConclusion cellSpace binderRename binderRelease

def RenameNeedsProfileRespects : Prop :=
  DigestRenameInvariant binderRename (fun _ : Bool => ()) ∧
  DigestCollisionFree (fun _ _ : Bool => True) (fun _ : Bool => ()) ∧
  ¬ RenameConclusion cellSpace binderRename binderRelease

def ReorderNeedsEffectAlgebraSound : Prop :=
  DigestOrderOnlyIfCommutes (fun _ _ : Nat => True) writePair List.sum ∧
  ¬ ReorderConclusion cellSpace (fun _ _ : Nat => True) writePair List.sum cellRelease

def ReorderNeedsDigestOrderOnlyIfCommutes : Prop :=
  EffectAlgebraSound (@Eq Nat) writePair cellRelease ∧
  ¬ ReorderConclusion cellSpace (@Eq Nat) writePair List.sum cellRelease

end RenameReorder
end SoftwareIsIncrementallySafe
