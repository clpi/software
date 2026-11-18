import Std

namespace RangeLedger.TileFrontier
-- r tiles of s raw samples partition the window. Query reads r totals;
-- remeasuring one dirty tile reads s raw samples when no delta is available.
abbrev legal (r s : Nat) := r * s = 4096
def dominates (a b r s : Nat) := a ≤ r ∧ b ≤ s ∧ (a < r ∨ b < s)

theorem incomparable {a b r s : Nat} (h : legal a b) (k : legal r s) :
    ¬ dominates a b r s := by
  unfold legal at *
  rintro ⟨ar,bs,strict⟩
  have bp : 0 < b := by cases b <;> simp_all
  have rp : 0 < r := by cases r <;> simp_all
  rcases strict with short | short
  · have lhs := Nat.mul_lt_mul_of_pos_right short bp
    have rhs := Nat.mul_le_mul_left r bs
    omega
  · have lhs := Nat.mul_le_mul_right b ar
    have rhs := Nat.mul_lt_mul_of_pos_left short rp
    omega

theorem minimax (r s : Nat) (h : legal r s) : 64 ≤ max r s := by
  unfold legal at h
  apply Classical.byContradiction; intro low
  have hr := Nat.le_max_left r s
  have hs := Nat.le_max_right r s
  have small := Nat.mul_le_mul (show r ≤ 63 by omega) (show s ≤ 63 by omega)
  omega

theorem attains : legal 64 64 ∧ max 64 64 = 64 ∧ legal 4096 1 ∧ max 4096 1 = 4096 := by decide
-- If signed edit deltas are already trusted, tile refresh can be one operation.
theorem different_contract : legal 1 4096 ∧ max 1 1 < max 64 64 := by decide
#print axioms incomparable
#print axioms minimax
#print axioms attains
end RangeLedger.TileFrontier
