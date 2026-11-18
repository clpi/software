import Qualification

set_option autoImplicit false

namespace IncrementalCert

def certClose {A : Type} (B : A → Prop) (R : List A → A → Prop) : A → Prop :=
  Qualification.Derives B R

theorem extensive {A : Type} {B : A → Prop} {R : List A → A → Prop} {a : A}
    (h : B a) : certClose B R a :=
  Qualification.Derives.root h

theorem monotone {A : Type} {B C : A → Prop} {R S : List A → A → Prop}
    (hb : ∀ a, B a → C a) (hr : ∀ ps a, R ps a → S ps a) :
    ∀ a, certClose B R a → certClose C S a :=
  Qualification.monotone hb hr

theorem idempotent {A : Type} (B : A → Prop) (R : List A → A → Prop) (a : A) :
    certClose (certClose B R) R a ↔ certClose B R a :=
  Qualification.idempotent B R a

theorem compounding {A : Type} (B C : A → Prop) (R : List A → A → Prop) (a : A) :
    certClose (fun x => B x ∨ C x) R a ↔
      certClose (fun x => certClose B R x ∨ certClose C R x) R a :=
  Qualification.compounding B C R a

theorem compounding_not_pointwise_union :
    ∃ (B C : Nat → Prop) (R : List Nat → Nat → Prop) (a : Nat),
      certClose (fun x => B x ∨ C x) R a ∧
        ¬ certClose B R a ∧ ¬ certClose C R a := by
  let R : List Nat → Nat → Prop := fun ps a => ps = [0, 1] ∧ a = 2
  let B : Nat → Prop := fun x => x = 0
  let C : Nat → Prop := fun x => x = 1
  refine ⟨B, C, R, 2, ?_, ?_, ?_⟩
  · refine Qualification.Derives.step (ps := [0, 1]) ?rule ?prem
    · exact ⟨rfl, rfl⟩
    · intro p hp
      simp at hp
      rcases hp with rfl | rfl
      · exact Qualification.Derives.root (Or.inl rfl)
      · exact Qualification.Derives.root (Or.inr rfl)
  · intro h
    have hclosed : Qualification.Closed R B := by
      intro ps a hr hp
      rcases hr with ⟨rfl, rfl⟩
      have h1 : (1 : Nat) = 0 := hp 1 (by simp)
      cases h1
    have h2 : (2 : Nat) = 0 := Qualification.least (fun _ hx => hx) hclosed 2 h
    cases h2
  · intro h
    have hclosed : Qualification.Closed R C := by
      intro ps a hr hp
      rcases hr with ⟨rfl, rfl⟩
      have h0 : (0 : Nat) = 1 := hp 0 (by simp)
      cases h0
    have h2 : (2 : Nat) = 1 := Qualification.least (fun _ hx => hx) hclosed 2 h
    cases h2

end IncrementalCert
