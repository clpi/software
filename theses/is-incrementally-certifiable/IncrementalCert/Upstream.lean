set_option autoImplicit false

namespace IncrementalCert
namespace Upstream

universe u
variable {A : Type u}

inductive Derives (B : A → Prop) (R : List A → A → Prop) : A → Prop where
  | root {a} : B a → Derives B R a
  | step {ps a} : R ps a → (∀ p, p ∈ ps → Derives B R p) → Derives B R a

def Closed (R : List A → A → Prop) (X : A → Prop) : Prop :=
  ∀ ps a, R ps a → (∀ p, p ∈ ps → X p) → X a

theorem least {B : A → Prop} {R : List A → A → Prop} {X : A → Prop}
    (roots : ∀ a, B a → X a) (rules : Closed R X) :
    ∀ a, Derives B R a → X a := by
  intro a h
  induction h with
  | root hb => exact roots _ hb
  | step hr _ ih => exact rules _ _ hr ih

theorem closed (B : A → Prop) (R : List A → A → Prop) :
    Closed R (Derives B R) := by
  intro ps a hr hp
  exact Derives.step hr hp

theorem extensive {B : A → Prop} {R : List A → A → Prop} {a : A}
    (h : B a) : Derives B R a :=
  Derives.root h

theorem monotone {B C : A → Prop} {R S : List A → A → Prop}
    (hb : ∀ a, B a → C a) (hr : ∀ ps a, R ps a → S ps a) :
    ∀ a, Derives B R a → Derives C S a := by
  apply least
  · intro a h
    exact Derives.root (hb a h)
  · intro ps a h hp
    exact Derives.step (hr ps a h) hp

theorem idempotent (B : A → Prop) (R : List A → A → Prop) (a : A) :
    Derives (Derives B R) R a ↔ Derives B R a := by
  constructor
  · exact least (fun _ h => h) (closed B R) a
  · exact Derives.root

theorem compounding (B C : A → Prop) (R : List A → A → Prop) (a : A) :
    Derives (fun x => B x ∨ C x) R a ↔
      Derives (fun x => Derives B R x ∨ Derives C R x) R a := by
  constructor
  · apply monotone _ (fun _ _ h => h) a
    intro x h
    cases h with
    | inl hb => exact Or.inl (Derives.root hb)
    | inr hc => exact Or.inr (Derives.root hc)
  · apply least _ (closed (fun x => B x ∨ C x) R) a
    intro x h
    cases h with
    | inl hb => exact monotone (fun _ h => Or.inl h) (fun _ _ h => h) x hb
    | inr hc => exact monotone (fun _ h => Or.inr h) (fun _ _ h => h) x hc

def noWorse (a b : Nat × Nat) : Prop :=
  a.1 ≤ b.1 ∧ a.2 ≤ b.2

theorem noWorse_trans {a b c : Nat × Nat}
    (hab : noWorse a b) (hbc : noWorse b c) : noWorse a c := by
  obtain ⟨h1, h2⟩ := hab
  obtain ⟨h3, h4⟩ := hbc
  exact ⟨Nat.le_trans h1 h3, Nat.le_trans h2 h4⟩

theorem noWorse_refl (a : Nat × Nat) : noWorse a a :=
  ⟨Nat.le_refl _, Nat.le_refl _⟩

end Upstream
end IncrementalCert
