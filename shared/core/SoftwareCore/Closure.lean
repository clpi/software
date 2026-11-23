/-
  SoftwareCore.Closure: the one canonical closure of the clpi/software-* theses.

  `Derives B R` is the least predicate containing the roots `B` and closed under
  the finite-premise rules `R`. Every thesis that defines its own derivation or
  closure is tied to this one by a bridge in `shared/core/bridges/` that imports
  the thesis's own module and proves the two equivalent.
-/
namespace SoftwareCore

universe u
variable {A : Type u}

inductive Derives (B : A → Prop) (R : List A → A → Prop) : A → Prop where
  | root {a : A} : B a → Derives B R a
  | step {ps : List A} {a : A} : R ps a → (∀ p, p ∈ ps → Derives B R p) → Derives B R a

/-- `X` is closed under the rules `R`. -/
def Closed (R : List A → A → Prop) (X : A → Prop) : Prop :=
  ∀ ps a, R ps a → (∀ p, p ∈ ps → X p) → X a

/-- Rules given as an explicit list of (premises, conclusion) pairs. -/
def ofPairs (rules : List (List A × A)) : List A → A → Prop :=
  fun ps a => (ps, a) ∈ rules

/-- Rules given as records with a premise list and a conclusion. -/
def ofRecords {E : Type u} (prem : E → List A) (concl : E → A) (es : List E) :
    List A → A → Prop :=
  fun ps a => ∃ e, e ∈ es ∧ prem e = ps ∧ concl e = a

theorem least {B : A → Prop} {R : List A → A → Prop} {X : A → Prop}
    (roots : ∀ a, B a → X a) (rules : Closed R X) :
    ∀ a, Derives B R a → X a := by
  intro a h
  induction h with
  | root hb => exact roots _ hb
  | step hr _ ih => exact rules _ _ hr ih

theorem closed (B : A → Prop) (R : List A → A → Prop) : Closed R (Derives B R) :=
  fun _ _ hr hp => Derives.step hr hp

/-- Two rule sets with the same instances derive the same facts. -/
theorem derives_congr {B : A → Prop} {R S : List A → A → Prop}
    (h : ∀ ps a, R ps a ↔ S ps a) (a : A) : Derives B R a ↔ Derives B S a := by
  constructor
  · intro d; induction d with
    | root hb => exact .root hb
    | step hr _ ih => exact .step ((h _ _).mp hr) ih
  · intro d; induction d with
    | root hb => exact .root hb
    | step hr _ ih => exact .step ((h _ _).mpr hr) ih

/-- Record-shaped rules mean the same as their (premises, conclusion) instances. -/
theorem ofRecords_iff {E : Type u} (prem : E → List A) (concl : E → A) (es : List E)
    (ps : List A) (a : A) :
    ofRecords prem concl es ps a ↔ ∃ e, e ∈ es ∧ prem e = ps ∧ concl e = a := Iff.rfl

end SoftwareCore
