import Std

namespace LogBatching
variable {α : Type}

-- Each output operation is allowed at most 64 fixed-size records.
def pack : List α → List (List α)
  | [] => []
  | x :: xs => (x :: xs.take 63) :: pack (xs.drop 63)
termination_by xs => xs.length
decreasing_by simp; omega

def single (xs : List α) := xs.map (fun x => [x])

theorem contents (xs : List α) : (pack xs).flatten = xs := by
  fun_induction pack xs with
  | case1 => simp [pack]
  | case2 x xs ih => simp [pack, ih]

theorem fits (xs : List α) : ∀ b ∈ pack xs, b.length ≤ 64 := by
  fun_induction pack xs with
  | case1 => simp [pack]
  | case2 x xs ih =>
    intro b hb
    rw [pack, List.mem_cons] at hb
    rcases hb with rfl | h
    · simp; omega
    · exact ih b h

theorem capacity (bs : List (List α)) (h : ∀ b ∈ bs, b.length ≤ 64) :
    bs.flatten.length ≤ bs.length * 64 := by
  induction bs with
  | nil => simp
  | cons x xs ih =>
    have headBound := h x (by simp)
    have tailBound := ih (fun b hb => h b (by simp [hb]))
    simp only [List.flatten_cons, List.length_append, List.length_cons]
    omega

theorem tight (xs : List α) : xs ≠ [] → ((pack xs).length - 1) * 64 < xs.length := by
  fun_induction pack xs with
  | case1 => simp
  | case2 x xs ih =>
    intro _
    rw [pack, List.length_cons, Nat.add_sub_cancel]
    by_cases h : xs.drop 63 = []
    · rw [h, pack]; simp
    · have lower := ih h
      have nonzero : 0 < (pack (xs.drop 63)).length := by
        cases hp : pack (xs.drop 63) with
        | nil =>
          have orig := contents (xs.drop 63)
          rw [hp] at orig
          exact False.elim (h orig.symm)
        | cons => simp
      simp only [List.length_drop, List.length_cons] at *
      omega

-- Every alternative, including one with variable chunk sizes, obeys this lower bound.
theorem minimum_writes (xs : List α) (bs : List (List α)) (same : bs.flatten = xs)
    (bounded : ∀ b ∈ bs, b.length ≤ 64) : (pack xs).length ≤ bs.length := by
  by_cases h : xs = []
  · simp [h,pack]
  have lhs := tight xs h
  have rhs := capacity bs bounded
  rw [same] at rhs
  omega

theorem before_after : (single (List.range 4096)).length = 4096 ∧
    (pack (List.range 4096)).length = 64 := by
  constructor
  · simp [single]
  · have upper := tight (List.range 4096) (by simp)
    have lower := capacity (pack (List.range 4096)) (fits _)
    rw [contents, List.length_range] at lower
    rw [List.length_range] at upper
    omega

#eval ((single (List.range 4096)).length, (pack (List.range 4096)).length)
#print axioms contents
#print axioms fits
#print axioms minimum_writes
#print axioms before_after
end LogBatching
