import SoftwareIsComposable

namespace SoftwareIsIncrementallyCertifiable

open SoftwareIsComposable

def c {ω : Type} (P : Profile ω → Prop) : Profile ω → Prop :=
  fun p => ∃ q, P q ∧ profileLE p q

theorem c_extensive {ω : Type} (P : Profile ω → Prop) (p : Profile ω) (hp : P p) : c P p :=
  ⟨p, hp, profileLE_refl p⟩

theorem c_monotone {ω : Type} {P Q : Profile ω → Prop}
    (h : ∀ p, P p → Q p) {p : Profile ω} (hp : c P p) : c Q p := by
  rcases hp with ⟨q, hq, hle⟩
  exact ⟨q, h q hq, hle⟩

theorem c_idempotent {ω : Type} (P : Profile ω → Prop) (p : Profile ω) :
    c (c P) p ↔ c P p := by
  constructor
  · intro h
    rcases h with ⟨q, hq, hpq⟩
    rcases hq with ⟨r, hr, hqr⟩
    exact ⟨r, hr, profileLE_trans hpq hqr⟩
  · intro h
    exact ⟨p, h, profileLE_refl p⟩

structure Cost where
  time : Nat
  compute : Nat

def paretoLE (a b : Cost) : Prop :=
  a.time ≤ b.time ∧ a.compute ≤ b.compute

def paretoDominates (a b : Cost) : Prop :=
  paretoLE a b ∧ (a.time < b.time ∨ a.compute < b.compute)

def noWorse (a b : Cost) : Prop :=
  paretoLE a b

theorem paretoLE_refl (a : Cost) : paretoLE a a :=
  ⟨Nat.le_refl _, Nat.le_refl _⟩

theorem paretoLE_trans {a b c : Cost} (hab : paretoLE a b) (hbc : paretoLE b c) :
    paretoLE a c :=
  ⟨Nat.le_trans hab.1 hbc.1, Nat.le_trans hab.2 hbc.2⟩

theorem paretoDominates_le {a b : Cost} (h : paretoDominates a b) : paretoLE a b :=
  h.1

theorem paretoDominates_irrefl (a : Cost) : ¬ paretoDominates a a := by
  intro h
  rcases h.2 with ht | hc
  · exact Nat.lt_irrefl _ ht
  · exact Nat.lt_irrefl _ hc

theorem equivalence_obligation_c {ω : Type} (P : Profile ω → Prop) (p : Profile ω) :
    c P p ↔ ∃ q, P q ∧ profileLE p q := Iff.rfl

theorem equivalence_obligation_pareto (a b : Cost) :
    noWorse a b ↔ a.time ≤ b.time ∧ a.compute ≤ b.compute := Iff.rfl

theorem equivalence_obligation_paretoDominates (a b : Cost) :
    paretoDominates a b ↔ noWorse a b ∧ (a.time < b.time ∨ a.compute < b.compute) := by
  simp [paretoDominates, noWorse]

structure Admission (ω : Type) where
  profile : Profile ω
  cost : Cost

def admits {ω : Type} (safe : Profile ω → Prop) (bound : Cost) (a : Admission ω) : Prop :=
  c safe a.profile ∧ noWorse a.cost bound

theorem admit_iff_closure_and_pareto {ω : Type}
    (safe : Profile ω → Prop) (bound : Cost) (a : Admission ω) :
    admits safe bound a ↔ c safe a.profile ∧ paretoLE a.cost bound := by
  simp [admits, noWorse]

theorem admitted_downward {ω : Type} {safe : Profile ω → Prop} {bound : Cost}
    {a b : Admission ω}
    (hA : admits safe bound a)
    (hp : profileLE b.profile a.profile)
    (hc : paretoLE b.cost a.cost) :
    admits safe bound b := by
  rcases hA with ⟨⟨q, hq, hqa⟩, hcost⟩
  exact ⟨⟨q, hq, profileLE_trans hp hqa⟩, paretoLE_trans hc hcost⟩

structure ClosureExport (ω : Type) where
  c : (Profile ω → Prop) → Profile ω → Prop
  extensive : ∀ P p, P p → c P p
  monotone : ∀ {P Q : Profile ω → Prop}, (∀ p, P p → Q p) → ∀ {p}, c P p → c Q p
  idempotent : ∀ P p, c (c P) p ↔ c P p

def canonicalClosure {ω : Type} : ClosureExport ω where
  c := c
  extensive := c_extensive
  monotone := fun h _ hp => c_monotone h hp
  idempotent := c_idempotent

theorem equivalence_obligation_closure {ω : Type} (P : Profile ω → Prop) (p : Profile ω) :
    canonicalClosure.c P p ↔ c P p := Iff.rfl

structure ParetoExport where
  le : Cost → Cost → Prop
  refl : ∀ a, le a a
  trans : ∀ a b c, le a b → le b c → le a c

def canonicalPareto : ParetoExport where
  le := paretoLE
  refl := paretoLE_refl
  trans := fun _ _ _ => paretoLE_trans

theorem equivalence_obligation_paretoExport (a b : Cost) :
    canonicalPareto.le a b ↔ paretoLE a b := Iff.rfl

structure SiblingPin where
  composable : String
  certifiableLocal : Bool
  optimality : String

def siblingPin : SiblingPin where
  composable := "033c12c01299a9b28983bee410c230641adc7d1e"
  certifiableLocal := true
  optimality := "aab49084e30757f39c7f9d7e4403522abf5ce46f"

end SoftwareIsIncrementallyCertifiable
