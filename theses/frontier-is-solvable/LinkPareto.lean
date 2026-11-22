/-
  Standing control (audited 2026-11-22). Link 2 audit: the two Pareto definitions.
  Audited at pins: software-frontier-is-solvable c7ffc6d03e8b (Frontier.lean: `Dominates`, `pareto`),
        software-is-quantifiable ba27febf48c8 (Pareto.lean: `dominates` on Nat × Nat),
        and, as a third definition found on the way, software-optimality af23f5d27990
        (HypergraphIncremental.lean: `dominates` on `Profile`).
  All three are IMPORTED here. In this repo it builds against the
  dependency revisions pinned in lakefile.lean.
-/
import Frontier
import SoftwareIsQuantifiable.Pareto
import HypergraphIncremental

open FrontierSolvable

namespace ParetoLinks

/-- The embedding of a quantifiable point as a two-axis integer cost
    (false = time, true = compute). -/
def natCost (p : Nat × Nat) : Bool → Int
  | false => (p.1 : Int)
  | true => (p.2 : Int)

/-- DERIVABLE: on every pair of points the two definitions agree, both the
    Prop form and the executable `pareto` over the axis list [time, compute]. -/
theorem quant_iff_frontier (p q : Nat × Nat) :
    SoftwareIsQuantifiable.Pareto.dominates p q ↔ Dominates natCost p q := by
  unfold SoftwareIsQuantifiable.Pareto.dominates Dominates NoWorse
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun i => ?_, ?_⟩
    · cases i <;> simp [natCost] <;> omega
    · rcases h3 with h | h
      · exact ⟨false, by simp [natCost]; omega⟩
      · exact ⟨true, by simp [natCost]; omega⟩
  · rintro ⟨hle, i, hi⟩
    have a := hle false
    have b := hle true
    simp [natCost] at a b
    refine ⟨by omega, by omega, ?_⟩
    cases i <;> simp [natCost] at hi
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)

theorem quant_iff_pareto (p q : Nat × Nat) :
    SoftwareIsQuantifiable.Pareto.dominates p q ↔ pareto [false, true] natCost p q = true := by
  rw [quant_iff_frontier, pareto_exact]
  unfold Dominates NoWorse
  constructor
  · rintro ⟨h, i, hi⟩; exact ⟨fun j _ => h j, i, by cases i <;> simp, hi⟩
  · rintro ⟨h, i, _, hi⟩; exact ⟨fun j => h j (by cases j <;> simp), i, hi⟩

/-- The other direction of the embedding: candidate costs projected to
    Nat × Nat with `Int.toNat`. -/
def point {A : Type} (cost : A → Bool → Int) (x : A) : Nat × Nat :=
  ((cost x false).toNat, (cost x true).toNat)

/-- DERIVABLE under one premise: nonnegative costs. -/
theorem frontier_iff_quant_of_nonneg {A : Type} (cost : A → Bool → Int)
    (nonneg : ∀ x i, 0 ≤ cost x i) (x y : A) :
    Dominates cost x y ↔ SoftwareIsQuantifiable.Pareto.dominates (point cost x) (point cost y) := by
  have e : ∀ z i, ((cost z i).toNat : Int) = cost z i := fun z i => Int.toNat_of_nonneg (nonneg z i)
  have hc : ∀ z i, cost z i = natCost (point cost z) i := by
    intro z i; cases i <;> simp [natCost, point, e]
  rw [quant_iff_frontier]
  unfold Dominates NoWorse
  simp only [← hc]

/-- FALSE without the premise: negative costs collapse under `toNat`.
    The repo's `Dominates` says x dominates y; quantifiable says no. -/
def negCost : Bool → Bool → Int
  | false, false => -2 | false, true => 0
  | true, false => -1 | true, true => 0

theorem toNat_breaks :
    Dominates negCost false true ∧
    ¬ SoftwareIsQuantifiable.Pareto.dominates (point negCost false) (point negCost true) := by
  refine ⟨⟨fun i => by cases i <;> decide, false, by decide⟩, ?_⟩
  simp [SoftwareIsQuantifiable.Pareto.dominates, point, negCost]

/-- Scope mismatch, not a definition mismatch: with one selected axis the
    repo's executable `pareto` judges a pair quantifiable's fixed two-axis
    relation does not. -/
theorem selected_axes_differ :
    pareto [false] natCost (1, 5) (2, 1) = true ∧
    ¬ SoftwareIsQuantifiable.Pareto.dominates (1, 5) (2, 1) := by
  refine ⟨by decide, ?_⟩
  simp [SoftwareIsQuantifiable.Pareto.dominates]

/-- Empty axes: the repo's `Dominates` over an empty index type never holds;
    quantifiable has no empty-axis case at all. -/
theorem empty_axes_never (cost : Nat → Empty → Int) (x y : Nat) : ¬ Dominates cost x y :=
  fun ⟨_, i, _⟩ => i.elim

/-! Third definition, the one the hypergraph module actually feeds:
    optimality's `Profile` dominance (eligibility and equal length inside). -/

def profileCost (p : HypergraphIncremental.Profile) (i : Nat) : Int := p.costs.getD i 0

/-- FALSE under the obvious total-function encoding when lengths differ:
    optimality says incomparable, the repo's `pareto` says x dominates y. -/
theorem profile_length_breaks :
    HypergraphIncremental.dominates ⟨true, [1]⟩ ⟨true, [1, 5]⟩ = false ∧
    pareto [0, 1] profileCost ⟨true, [1]⟩ ⟨true, [1, 5]⟩ = true := by
  decide

/-- And eligibility is inside optimality's relation but outside the repo's. -/
theorem profile_eligibility_differs :
    HypergraphIncremental.dominates ⟨false, [0, 0]⟩ ⟨true, [1, 1]⟩ = false ∧
    pareto [0, 1] profileCost ⟨false, [0, 0]⟩ ⟨true, [1, 1]⟩ = true := by
  decide

end ParetoLinks

#print axioms ParetoLinks.quant_iff_frontier
#print axioms ParetoLinks.quant_iff_pareto
#print axioms ParetoLinks.frontier_iff_quant_of_nonneg
#print axioms ParetoLinks.toNat_breaks
#print axioms ParetoLinks.selected_axes_differ
#print axioms ParetoLinks.empty_axes_never
#print axioms ParetoLinks.profile_length_breaks
#print axioms ParetoLinks.profile_eligibility_differs
