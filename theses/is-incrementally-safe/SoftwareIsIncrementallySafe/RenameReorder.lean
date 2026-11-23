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

theorem sameSymbolSameProfile {Symbol Measure : Type} :
    ∀ {R : Release Symbol Measure}, uniqueSymbols R →
      ∀ {p q : Profile Symbol Measure}, p ∈ R → q ∈ R → p.symbol = q.symbol → p = q
  | [], _, _, _, hp, _, _ => nomatch hp
  | r :: rs, hU, p, q, hp, hq, hs => by
    unfold uniqueSymbols at hU
    rw [List.map_cons, List.nodup_cons] at hU
    have hrest : uniqueSymbols rs := hU.2
    cases hp with
    | head =>
      cases hq with
      | head => rfl
      | tail _ hq' => exact absurd (hs ▸ List.mem_map_of_mem hq') hU.1
    | tail _ hp' =>
      cases hq with
      | head => exact absurd (hs ▸ List.mem_map_of_mem hp') hU.1
      | tail _ hq' => exact sameSymbolSameProfile hrest hp' hq' hs

theorem zeroDeltaRefl {Symbol Measure : Type} {space : MeasureSpace Measure}
    {R : Release Symbol Measure} (h : WellFormed space R) : ZeroDelta space R R := by
  have hle := releaseLe_refl (space := space) h.1 h.2
  have hnd : ¬ releaseDominates space R R := by
    rintro ⟨_, q, hq, p, hp, hd⟩
    have hpq := sameSymbolSameProfile h.1 hp hq hd.1.1.1
    subst hpq
    exact not_dominates_self space p hd
  exact ⟨hle, hle, hnd, hnd⟩

theorem frontierInvariantRefl {Symbol Measure : Type} [DecidableEq Symbol]
    {space : MeasureSpace Measure} {R : Release Symbol Measure} :
    FrontierInvariant space R R :=
  fun _ _ => Iff.rfl

theorem renameZeroDelta {Prog Binder Digest Symbol Measure : Type} [DecidableEq Symbol]
    (space : MeasureSpace Measure)
    (rename : Renaming Binder → Prog → Prog) (digest : Prog → Digest)
    (equiv : Prog → Prog → Prop) (profileOf : Prog → Release Symbol Measure) :
    RenameZeroDelta space rename digest equiv profileOf := by
  intro hInv hFree hResp σ p hWF
  have heq : profileOf (rename σ p) = profileOf p :=
    hResp _ _ (hFree _ _ (hInv σ p))
  rw [heq]
  exact ⟨rfl, zeroDeltaRefl hWF, frontierInvariantRefl⟩

theorem commutingReorderZeroDelta {Effect Prog Digest Symbol Measure : Type}
    [DecidableEq Symbol] (space : MeasureSpace Measure)
    (commutes : Effect → Effect → Prop) (ctx : Effect → Effect → Prog)
    (digest : Prog → Digest) (profileOf : Prog → Release Symbol Measure) :
    CommutingReorderZeroDelta space commutes ctx digest profileOf := by
  intro hSound hOrder e₁ e₂ hWF
  have commuting : commutes e₁ e₂ →
      ZeroDelta space (profileOf (ctx e₁ e₂)) (profileOf (ctx e₂ e₁)) ∧
      FrontierInvariant space (profileOf (ctx e₁ e₂)) (profileOf (ctx e₂ e₁)) := by
    intro hc
    rw [← hSound e₁ e₂ hc]
    exact ⟨zeroDeltaRefl hWF, frontierInvariantRefl⟩
  exact ⟨commuting, fun hd => (commuting (hOrder e₁ e₂ hd)).1⟩

theorem singletonWellFormed (n : Nat) :
    WellFormed cellSpace [({ symbol := (), readings := [n], observed := true } : Profile Unit Unit)] :=
  ⟨by simp [uniqueSymbols], fun p hp => by
    simp only [List.mem_singleton] at hp
    subst hp
    rfl⟩

theorem binderReleaseWellFormed (b : Bool) : WellFormed cellSpace (binderRelease b) :=
  singletonWellFormed _

theorem negationNotZeroDelta :
    ¬ ZeroDelta cellSpace (binderRelease (binderRename negation true)) (binderRelease true) := by
  intro h
  obtain ⟨p, hp, hnw⟩ := h.2.1.2.2.2.2 _ List.mem_cons_self
  simp only [binderRename, negation, binderRelease, List.mem_singleton] at hp
  subst hp
  have hax := hnw.1.2
  simp [axesLe, axisLe, cellSpace, binderRename, negation] at hax

theorem negationBreaksConclusion :
    ¬ RenameConclusion cellSpace binderRename binderRelease :=
  fun h => negationNotZeroDelta (h negation true (binderReleaseWellFormed true)).2.1

theorem renameNeedsDigestRenameInvariant : RenameNeedsDigestRenameInvariant :=
  ⟨fun _ _ h => h, fun _ _ h => h ▸ rfl, negationBreaksConclusion⟩

theorem renameNeedsDigestCollisionFree : RenameNeedsDigestCollisionFree :=
  ⟨fun _ _ => rfl, fun _ _ h => h ▸ rfl, negationBreaksConclusion⟩

theorem renameNeedsProfileRespects : RenameNeedsProfileRespects :=
  ⟨fun _ _ => rfl, fun _ _ _ => trivial, negationBreaksConclusion⟩

theorem cellReleaseWellFormed (writes : List Nat) : WellFormed cellSpace (cellRelease writes) :=
  singletonWellFormed _

theorem nonCommutingNotZeroDelta :
    ¬ ZeroDelta cellSpace (cellRelease (writePair 1 2)) (cellRelease (writePair 2 1)) :=
  fun h => nonCommutingChangesProfile.2.1 h.1

theorem reorderNeedsEffectAlgebraSound : ReorderNeedsEffectAlgebraSound :=
  ⟨fun _ _ _ => trivial, fun h =>
    nonCommutingNotZeroDelta ((h 1 2 (cellReleaseWellFormed _)).1 trivial).1⟩

theorem reorderNeedsDigestOrderOnlyIfCommutes : ReorderNeedsDigestOrderOnlyIfCommutes :=
  ⟨fun _ _ h => h ▸ rfl, fun h =>
    nonCommutingNotZeroDelta ((h 1 2 (cellReleaseWellFormed _)).2 unorderedDigestUnsound.1)⟩

end RenameReorder
end SoftwareIsIncrementallySafe
