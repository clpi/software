import Std

namespace RangeLedger.OverlapPlan
abbrev World := Nat → Int
inductive Page where | left | overlap | right deriving DecidableEq, Repr
open Page
def read (p : World) : Page → Int
  | left => p 3072 - p 0
  | overlap => p 3072 - p 1024
  | right => p 4096 - p 1024
def solve (x y z : Int) := x-y+z

theorem reconstruction (p : World) :
    solve (read p left) (read p overlap) (read p right) = p 4096 - p 0 := by
  simp [solve,read]; omega

-- For each missing page there are two indistinguishable worlds with different totals.
def other : Page → World
  | left => fun i => if i = 0 then 1 else 0
  | overlap => fun i => if i = 0 || i = 3072 then 1 else 0
  | right => fun i => if i = 4096 then 1 else 0

theorem essential (missing : Page) :
    (∀ j, j ≠ missing → read (fun _ => 0) j = read (other missing) j) ∧
    other missing 4096 - other missing 0 ≠ 0 := by
  constructor
  · intro j; cases missing <;> cases j <;> decide
  · cases missing <;> decide

theorem control : solve 120 50 90 = 160 ∧ (120+50+90 : Int) ≠ 160 := by decide
#print axioms reconstruction
#print axioms essential
#print axioms control
end RangeLedger.OverlapPlan
