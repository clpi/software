import Std

namespace RangeLedger.GroupedEdits

private theorem sumAppend (xs ys : List Int) : (xs ++ ys).sum = xs.sum + ys.sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]; omega
abbrev Row := Nat × Int
def part (k : Nat) (r : Row) := if k = r.1 then r.2 else 0
def agg (k : Nat) (rows : List Row) := (rows.map (part k)).sum
def image (k : Nat) (r : Option Row) := (r.map (part k)).getD 0
def patch (k : Nat) (old new : Option Row) (cached : Int) := cached - image k old + image k new

theorem splice (k : Nat) (left right : List Row) (old new : Option Row) :
    patch k old new (agg k (left ++ old.toList ++ right)) =
      agg k (left ++ new.toList ++ right) := by
  cases old <;> cases new <;> simp [patch,agg,image,sumAppend] <;> omega

def before : Row := (2,19)
def afterRow : Row := (3,24)
theorem move : patch 2 (some before) (some afterRow) 100 = 81 ∧
    patch 3 (some before) (some afterRow) 90 = 114 := by decide
theorem old_image_required :
    patch 2 (some (2,19)) (some afterRow) 100 ≠ patch 2 (some (2,20)) (some afterRow) 100 := by decide

-- Any exact writer must change the two unequal group totals in this move.
theorem both_writes (out : Nat → Int) (ok2 : out 2 = 81) (ok3 : out 3 = 114) :
    out 2 ≠ 100 ∧ out 3 ≠ 90 := by omega
#eval (patch 2 (some before) (some afterRow) 100, patch 3 (some before) (some afterRow) 90)
#print axioms splice
#print axioms move
#print axioms both_writes
#print axioms old_image_required
end RangeLedger.GroupedEdits
