import Qualification

/- Tests are obligations or evidence-producing experiments, not interchangeable.
   This module proves exact redundancy for encoded obligations and supports.
   Atom contains exact context, lineage, effects, premises, trust and polarity.
   R is a single directed hypergraph relation; its premise lists are conjunctive.
-/
namespace TestingRedundancy
open Qualification
universe u v
variable {Atom : Type u} {Model : Type v}

def Join (B T : Atom → Prop) : Atom → Prop := fun a => B a ∨ T a

def Covered (B : Atom → Prop) (R : List Atom → Atom → Prop)
    (T : Atom → Prop) : Prop := ∀ a, T a → Derives B R a

-- Necessary AND sufficient: a suite adds no derived qualification exactly when
-- every one of its obligations already has support. Authorship is irrelevant.
theorem redundancy_iff (B T : Atom → Prop) (R : List Atom → Atom → Prop) :
    Covered B R T ↔ ∀ a, Derives (Join B T) R a ↔ Derives B R a := by
  constructor
  · intro covered a
    constructor
    · apply least _ (closed B R) a
      intro x hx
      cases hx with
      | inl hb => exact Derives.root hb
      | inr ht => exact covered x ht
    · exact monotone (fun _ h => Or.inl h) (fun _ _ h => h) a
  · intro same a ht
    exact (same a).mp (Derives.root (Or.inr ht))

-- Redundancy is stable under ANY further evidence and even new rules, provided
-- rules only expand and all previous certificates remain valid.
theorem contextual_redundancy (B T F : Atom → Prop)
    (R S : List Atom → Atom → Prop) (covered : Covered B R T)
    (extension : ∀ ps a, R ps a → S ps a) :
    ∀ a, Derives (Join (Join B F) T) S a ↔ Derives (Join B F) S a := by
  apply (redundancy_iff (Join B F) T S).mp
  intro a ht
  exact monotone (fun _ h => Or.inl h) extension a (covered a ht)

-- Equality of closure is a congruence for future compounding, not merely an
-- agreement on today's displayed color.
theorem compounding_congruence (B C F : Atom → Prop)
    (R : List Atom → Atom → Prop)
    (same : ∀ a, Derives B R a ↔ Derives C R a) :
    ∀ a, Derives (Join B F) R a ↔ Derives (Join C F) R a := by
  intro a
  constructor
  · apply least _ (closed (Join C F) R) a
    intro x hx
    cases hx with
    | inl hb =>
      exact monotone (fun _ h => Or.inl h) (fun _ _ h => h) x
        ((same x).mp (Derives.root hb))
    | inr hf => exact Derives.root (Or.inr hf)
  · apply least _ (closed (Join B F) R) a
    intro x hx
    cases hx with
    | inl hc =>
      exact monotone (fun _ h => Or.inl h) (fun _ _ h => h) x
        ((same x).mpr (Derives.root hc))
    | inr hf => exact Derives.root (Or.inr hf)

-- Exact model-theoretic characterization, no assumed solver completeness.
-- The least hypergraph closure itself is a model and separates every missing
-- obligation. Models here mean all closed sets, not arbitrary real executions.
def IsModel (B : Atom → Prop) (R : List Atom → Atom → Prop)
    (X : Atom → Prop) : Prop := (∀ a, B a → X a) ∧ Closed R X

theorem derivable_iff_all_models (B : Atom → Prop)
    (R : List Atom → Atom → Prop) (a : Atom) :
    Derives B R a ↔ ∀ X, IsModel B R X → X a := by
  constructor
  · intro h X hm
    exact least hm.1 hm.2 a h
  · intro all
    exact all (Derives B R) ⟨fun _ => Derives.root, closed B R⟩

theorem missing_obligation_has_countermodel (B : Atom → Prop)
    (R : List Atom → Atom → Prop) (a : Atom) (missing : ¬ Derives B R a) :
    ∃ X, IsModel B R X ∧ ¬ X a :=
  ⟨Derives B R, ⟨fun _ => Derives.root, closed B R⟩, missing⟩

-- Distinguish logical redundancy from a new empirical run. The latter adds
-- a new observation atom, unless it is itself already derived.
theorem singleton_duplicate (B : Atom → Prop) (R : List Atom → Atom → Prop)
    (x : Atom) (hx : Derives B R x) :
    ∀ a, Derives (Join B (fun y => y = x)) R a ↔ Derives B R a := by
  apply (redundancy_iff B (fun y => y = x) R).mp
  intro y hy
  subst y
  exact hx

theorem novel_witness_strict (B : Atom → Prop) (R : List Atom → Atom → Prop)
    (x : Atom) (hx : ¬ Derives B R x) :
    (∀ a, Derives B R a → Derives (Join B (fun y => y = x)) R a) ∧
    (Derives (Join B (fun y => y = x)) R x ∧ ¬ Derives B R x) := by
  exact ⟨monotone (fun _ h => Or.inl h) (fun _ _ h => h),
    Derives.root (Or.inr rfl), hx⟩

-- A suite is a predicate on models. This exact criterion covers generated or
-- manual tests, acceptance, failure and any additional independent oracle.
def Entails (E T : Model → Prop) : Prop := ∀ m, E m → T m

theorem acceptance_unchanged_iff (E T : Model → Prop) :
    Entails E T ↔ (fun m => E m ∧ T m) = E := by
  constructor
  · intro h
    funext m
    exact propext ⟨And.left, fun em => ⟨em, h m em⟩⟩
  · intro h m em
    have hm : E m ∧ T m := by
      have he := congrFun h m
      exact he.mpr em
    exact hm.2

-- Direct deterministic qualification views, including lawful/unlawful support,
-- conflict and unknown, are preserved. The view is derived, not separate data.
theorem every_derived_view_preserved {View : Sort v}
    (B T : Atom → Prop) (R : List Atom → Atom → Prop)
    (covered : Covered B R T) (view : (Atom → Prop) → View) :
    view (Derives (Join B T) R) = view (Derives B R) := by
  have h : Derives (Join B T) R = Derives B R := by
    funext a
    exact propext ((redundancy_iff B T R).mp covered a)
  rw [h]

-- No function of an observation can recover a qualification that distinguishes
-- two models having identical observations. Even a finite two-model world suffices.
theorem observational_independence {Observation : Type u}
    (observe : Model → Observation) (qualify : Model → Bool)
    (m₁ m₂ : Model) (same : observe m₁ = observe m₂)
    (different : qualify m₁ ≠ qualify m₂) :
    ¬ ∃ infer : Observation → Bool, ∀ m, infer (observe m) = qualify m := by
  rintro ⟨infer, correct⟩
  apply different
  calc qualify m₁ = infer (observe m₁) := (correct m₁).symm
       _ = infer (observe m₂) := congrArg infer same
       _ = qualify m₂ := correct m₂

#print axioms redundancy_iff
#print axioms contextual_redundancy
#print axioms compounding_congruence
#print axioms derivable_iff_all_models
#print axioms missing_obligation_has_countermodel
#print axioms every_derived_view_preserved
#print axioms observational_independence
end TestingRedundancy
