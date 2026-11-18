import Redundancy

namespace BenchmarkRedundancy
open Qualification TestingRedundancy
universe u v
variable {Atom : Type u}

-- Scope is part of the atom, not an inherited display label.
structure Context where
  artifact : Nat
  workload : Nat
  venue : Nat
  epoch : Nat
  protocol : Nat
  deriving DecidableEq, Repr

structure Receipt where
  context : Context
  sample : Nat
  metric : Nat
  value : Nat
  deriving DecidableEq, Repr

-- A plan denotes a stated result, not a claim that execution will produce it.
structure Plan (Atom : Type u) (Axis : Type v) where
  evidence : Atom → Prop
  cost : Axis → Nat

def Supports (B : Atom → Prop) (R : List Atom → Atom → Prop)
    (p : Plan Atom Axis) (purpose : Atom → Prop) : Prop :=
  ∀ a, purpose a → Derives (Join B p.evidence) R a

def Covers (B : Atom → Prop) (R : List Atom → Atom → Prop)
    (p q : Plan Atom Axis) : Prop :=
  ∀ a, q.evidence a → Derives (Join B p.evidence) R a

def NoWorse (p q : Plan Atom Axis) : Prop := ∀ i, p.cost i ≤ q.cost i

def Dominates (B : Atom → Prop) (R : List Atom → Atom → Prop)
    (p q : Plan Atom Axis) : Prop :=
  Covers B R p q ∧ NoWorse p q ∧ ∃ i, p.cost i < q.cost i

theorem coverage_preserves_purpose {B : Atom → Prop}
    {R : List Atom → Atom → Prop} {p q : Plan Atom Axis}
    (h : Covers B R p q) {purpose : Atom → Prop}
    (hq : Supports B R q purpose) : Supports B R p purpose := by
  intro a ha
  apply least (X := Derives (Join B p.evidence) R) _ (closed _ _) a (hq a ha)
  intro x hx
  cases hx with
  | inl hb => exact Derives.root (Or.inl hb)
  | inr hq => exact h x hq

def Pareto (B : Atom → Prop) (R : List Atom → Atom → Prop)
    (admitted : Plan Atom Axis → Prop) (q : Plan Atom Axis) : Prop :=
  admitted q ∧ ¬ ∃ p, admitted p ∧ Dominates B R p q

theorem dominated_not_pareto {B : Atom → Prop} {R : List Atom → Atom → Prop}
    {admitted : Plan Atom Axis → Prop} {p q : Plan Atom Axis}
    (hp : admitted p) (hd : Dominates B R p q) : ¬ Pareto B R admitted q := by
  intro hq
  exact hq.2 ⟨p, hp, hd⟩

def skip (Axis : Type v) : Plan Atom Axis := ⟨fun _ => False, fun _ => 0⟩

-- If all outcomes claimed by q are already certified and one declared cost
-- is positive, omitting q dominates it. Skip must separately be admissible.
theorem covered_positive_plan_dominated {B : Atom → Prop}
    {R : List Atom → Atom → Prop} {q : Plan Atom Axis}
    (covered : Covered B R q.evidence) (positive : ∃ i, 0 < q.cost i) :
    Dominates B R (skip Axis) q := by
  refine ⟨?_, ?_, positive⟩
  · intro a ha
    exact monotone (fun _ h => Or.inl h) (fun _ _ h => h) a (covered a ha)
  · intro i; exact Nat.zero_le _

-- Every possible outcome must be covered before eliminating an experiment
-- prospectively; observing one covered result is not enough.
theorem all_outcomes_redundant {Outcome : Type v}
    (B : Atom → Prop) (R : List Atom → Atom → Prop)
    (results : Outcome → Atom → Prop)
    (covered : ∀ o, Covered B R (results o)) :
    ∀ o a, Derives (Join B (results o)) R a ↔ Derives B R a := by
  intro o
  exact (redundancy_iff B (results o) R).mp (covered o)

-- Purpose-relative redundancy may be weaker than total evidence redundancy.
def PurposeRedundant (B : Atom → Prop) (R : List Atom → Atom → Prop)
    (results purpose : Atom → Prop) : Prop :=
  ∀ a, purpose a → (Derives (Join B results) R a ↔ Derives B R a)

theorem covered_implies_purpose_redundant (B results purpose : Atom → Prop)
    (R : List Atom → Atom → Prop) (h : Covered B R results) :
    PurposeRedundant B R results purpose := by
  intro a _
  exact (redundancy_iff B results R).mp h a

-- Adding the same surrounding cost preserves coordinate inequalities and strictness.
-- This applies only when the stated accounting really is additive.
def appendCost (p : Plan Atom Axis) (overhead : Axis → Nat) : Plan Atom Axis :=
  { p with cost := fun i => p.cost i + overhead i }

theorem additive_context_preserves_dominance {B : Atom → Prop}
    {R : List Atom → Atom → Prop} {p q : Plan Atom Axis}
    (h : Dominates B R p q) (overhead : Axis → Nat) :
    Dominates B R (appendCost p overhead) (appendCost q overhead) := by
  refine ⟨h.1, ?_, ?_⟩
  · intro i; exact Nat.add_le_add_right (h.2.1 i) _
  · obtain ⟨i, hi⟩ := h.2.2
    exact ⟨i, Nat.add_lt_add_right hi _⟩

-- Semantic validity is a separate premise, never inferred from an identical hash.
theorem derived_result_sound (B : Atom → Prop) (R : List Atom → Atom → Prop)
    (trueAt : Atom → Prop) (roots : ∀ a, B a → trueAt a)
    (certificates : Closed R trueAt) (a : Atom) (h : Derives B R a) : trueAt a :=
  soundness roots certificates a h

-- No certificates means exactly the actual roots, not cross-context transfer.
theorem no_rules_iff (B : Atom → Prop) (a : Atom) :
    Derives B (fun _ _ => False) a ↔ B a := by
  constructor
  · exact least (fun _ h => h) (fun _ _ h _ => h.elim) a
  · exact Derives.root

-- A new sample identity cannot be fabricated by replaying an old receipt.
theorem fresh_sample_not_derived (old fresh : Receipt)
    (different : old.sample ≠ fresh.sample) :
    ¬ Derives (fun r => r = old) (fun _ _ => False) fresh := by
  intro h
  have eq := (no_rules_iff (fun r => r = old) fresh).mp h
  exact different (congrArg Receipt.sample eq).symm

theorem stale_context_not_derived (old fresh : Receipt)
    (different : old.context ≠ fresh.context) :
    ¬ Derives (fun r => r = old) (fun _ _ => False) fresh := by
  intro h
  have eq := (no_rules_iff (fun r => r = old) fresh).mp h
  exact different (congrArg Receipt.context eq).symm

end BenchmarkRedundancy
#print axioms BenchmarkRedundancy.coverage_preserves_purpose
#print axioms BenchmarkRedundancy.covered_positive_plan_dominated
#print axioms BenchmarkRedundancy.all_outcomes_redundant
#print axioms BenchmarkRedundancy.additive_context_preserves_dominance
#print axioms BenchmarkRedundancy.fresh_sample_not_derived
