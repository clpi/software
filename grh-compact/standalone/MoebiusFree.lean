import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Finset

/-- If every lower sum `∑_{B' ≤ B} F B'` vanishes then `F` vanishes, by well-founded induction:
the sum below `B` is `F B` plus sums that already vanish. No incidence algebra. -/
lemma New.eq_zero_of_forall_sum_Iic_eq_zero {α : Type*} [PartialOrder α] [LocallyFiniteOrderBot α]
    [WellFoundedLT α] (F : α → ℤ) (h : ∀ B, 0 = ∑ B' ∈ Iic B, F B') (B : α) : F B = 0 := by
  induction B using WellFoundedLT.induction with
  | _ B ih =>
    have h_lt : ∑ B' ∈ Iio B, F B' = 0 := sum_eq_zero fun B' hB' ↦ ih B' (mem_Iio.1 hB')
    have := h B
    rw [Iic_eq_cons_Iio, sum_cons, h_lt, add_zero] at this
    exact this.symm
