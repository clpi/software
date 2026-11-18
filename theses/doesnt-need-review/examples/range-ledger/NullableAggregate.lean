import Std

namespace RangeLedger.NullableAggregate

private theorem sumAppend (xs ys : List Int) : (xs ++ ys).sum = xs.sum + ys.sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]; omega
-- SQL SUM over signed integers with exact intermediate arithmetic.
def plus : Option Int → Option Int → Option Int
  | none,y => y
  | x,none => x
  | some x,some y => some (x+y)

def sql : List (Option Int) → Option Int
  | [] => none
  | x::xs => plus x (sql xs)
def sum0 (xs : List (Option Int)) := (xs.map (fun x => x.getD 0)).sum
def seen (xs : List (Option Int)) := xs.any Option.isSome
def decode (s : Int) (present : Bool) : Option Int := if present then some s else none

theorem summary (xs : List (Option Int)) : decode (sum0 xs) (seen xs) = sql xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases x with
    | none => simpa [sql,plus,decode,sum0,seen] using ih
    | some v =>
      have zero : seen xs = false → sum0 xs = 0 := by
        clear ih; clear v
        induction xs with
        | nil => simp [sum0]
        | cons x xs ih => cases x <;> simp_all [seen,sum0]
      rw [sql,← ih]
      cases hx : seen xs <;> simp_all [decode,plus,sum0,seen]

theorem one_bit_necessary : ¬ ∃ f : Int → Option Int, ∀ xs, f (sum0 xs) = sql xs := by
  rintro ⟨f,h⟩
  have a := h [none]
  have b := h [some 7,some (-7)]
  exact absurd (a.symm.trans b) (by decide)

theorem merge (xs ys : List (Option Int)) :
    decode (sum0 xs + sum0 ys) (seen xs || seen ys) = sql (xs++ys) := by
  rw [← summary]
  simp [sum0,seen,sumAppend]
#print axioms summary
#print axioms one_bit_necessary
#print axioms merge
end RangeLedger.NullableAggregate
