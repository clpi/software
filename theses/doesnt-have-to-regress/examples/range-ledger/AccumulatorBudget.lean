import Std

namespace RangeLedger.AccumulatorBudget

private theorem sumAppend (xs ys : List Nat) : (xs ++ ys).sum = xs.sum + ys.sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]; omega
-- Raw unsigned telemetry samples occupy one byte. Each 16-bit lane is flushed
-- into a wider exact accumulator before it wraps.
def lane (xs : List Nat) := xs.sum % 65536
def bytesOK (xs : List Nat) := ∀ x ∈ xs, x ≤ 255

theorem sum_bound (xs : List Nat) (bounded : bytesOK xs) : xs.sum ≤ xs.length * 255 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have h := bounded x (by simp)
    have t := ih (fun v hv => bounded v (by simp [hv]))
    simp only [List.sum_cons,List.length_cons]; omega

theorem lane_exact (xs : List Nat) (bounded : bytesOK xs) (cap : xs.length ≤ 257) :
    lane xs = xs.sum := by
  have b := sum_bound xs bounded
  exact Nat.mod_eq_of_lt (by omega)

theorem combine (chunks : List (List Nat)) (ok : ∀ xs ∈ chunks, bytesOK xs ∧ xs.length ≤ 257) :
    (chunks.map lane).sum = chunks.flatten.sum := by
  induction chunks with
  | nil => rfl
  | cons x xs ih =>
    have h := ok x (by simp)
    have t := ih (fun v hv => ok v (by simp [hv]))
    simp [lane_exact x h.1 h.2,t,sumAppend]

set_option maxRecDepth 2048 in
theorem cap_tight : lane (List.replicate 258 255) = 254 ∧ (List.replicate 258 255).sum = 65790 := by decide
theorem flush_lower (calls : Nat) (capacity : 4096 ≤ calls*257) : 16 ≤ calls := by omega
theorem counts : (4096+63)/64 = 64 ∧ (4096+256)/257 = 16 := by decide
#print axioms lane_exact
#print axioms combine
#print axioms cap_tight
#print axioms flush_lower
end RangeLedger.AccumulatorBudget
