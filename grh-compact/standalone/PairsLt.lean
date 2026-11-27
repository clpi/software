import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Choose.Sum

open Finset

/-- The number of pairs `a < b` in `Fin r` is `r.choose 2`, counted row by row. -/
lemma New.sum_sum_ite_lt_fin (r : ℕ) :
    ∑ a : Fin r, ∑ b : Fin r, (if a < b then 1 else 0) = r.choose 2 := by
  have h_row (a : Fin r) : ∑ b : Fin r, (if a < b then 1 else 0) = r - 1 - a := by
    rw [sum_boole, Nat.cast_id, ← Fin.card_Ioi]
    congr 1
    ext b
    simp
  simp only [h_row]
  rw [Fin.sum_univ_eq_sum_range (fun i ↦ r - 1 - i) r, ← sum_range_reflect, Nat.choose_two_right,
    ← sum_range_id]
  refine sum_congr rfl fun i hi ↦ ?_
  have := mem_range.1 hi
  omega
