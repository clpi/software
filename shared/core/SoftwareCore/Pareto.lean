/-
  SoftwareCore.Pareto: the one canonical no-worse and domination order on cost
  vectors. Bridges in `shared/core/bridges/` tie each thesis's own version to it.
-/
namespace SoftwareCore

universe u v
variable {I : Type u} {α : Type v}

/-- `x` is no worse than `y` on every axis (lower is better). -/
def NoWorse [LE α] (x y : I → α) : Prop := ∀ i, x i ≤ y i

/-- `x` dominates `y`: no worse everywhere, strictly better somewhere. -/
def Dominates [LE α] [LT α] (x y : I → α) : Prop := NoWorse x y ∧ ∃ i, x i < y i

/-- A pair read as a two-axis cost vector. -/
def pairVec (p : α × α) : Bool → α := fun b => if b then p.1 else p.2

theorem noWorse_pair [LE α] (x y : α × α) :
    NoWorse (pairVec x) (pairVec y) ↔ x.1 ≤ y.1 ∧ x.2 ≤ y.2 := by
  constructor
  · intro h; exact ⟨h true, h false⟩
  · intro ⟨h1, h2⟩ b; cases b
    · exact h2
    · exact h1

theorem dominates_irrefl_nat (x : I → Nat) : ¬ Dominates x x := by
  intro ⟨_, i, h⟩; exact Nat.lt_irrefl _ h

theorem dominates_irrefl_int (x : I → Int) : ¬ Dominates x x := by
  intro ⟨_, i, h⟩; exact Int.lt_irrefl _ h

end SoftwareCore
