import Std

namespace RangeLedger.AffineCalibration

-- Signed cost gap = candidate - incumbent. Zero and full load are paired runs.
def gap (setup per : Int) (n : Nat) : Int := setup + per * n

theorem endpoints (setup per : Int) (limit : Nat) :
    (∀ n ≤ limit, gap setup per n ≤ 0) ↔ gap setup per 0 ≤ 0 ∧ gap setup per limit ≤ 0 := by
  constructor
  · intro all; exact ⟨all 0 (by omega),all limit (by omega)⟩
  · rintro ⟨first,last⟩ n hn
    simp only [gap,Int.ofNat_zero,Int.mul_zero,Int.add_zero] at *
    by_cases h : 0 ≤ per
    · have le := Int.mul_le_mul_of_nonneg_left (show (n : Int) ≤ limit by omega) h
      omega
    · have le := Int.mul_nonpos_of_nonpos_of_nonneg (show per ≤ 0 by omega) (show 0 ≤ (n : Int) by omega)
      omega

-- At any single sampled load, an affine losing curve can agree with a zero gap.
theorem one_pair_insufficient (k : Nat) (valid : k ≤ 4096) :
    ∃ a b : Int, gap a b k = 0 ∧ ∃ n ≤ 4096, 0 < gap a b n := by
  by_cases hk : k = 4096
  · subst k; exact ⟨4096,-1,by decide,0,by decide,by decide⟩
  · refine ⟨-(k : Int),1,by simp [gap]; omega,4096,by decide,?_⟩
    simp [gap]; omega

def nonLinear (n : Nat) : Int := if n = 2048 then 1 else -1
theorem out_of_scope : nonLinear 0 < 0 ∧ nonLinear 4096 < 0 ∧ nonLinear 2048 > 0 := by decide
#print axioms endpoints
#print axioms one_pair_insufficient
#print axioms out_of_scope
end RangeLedger.AffineCalibration
