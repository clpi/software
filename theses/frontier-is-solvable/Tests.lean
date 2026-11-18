import Frontier
open FrontierSolvable
namespace FrontierTests
-- Named identities 0 and 3 tie. Identity 1 trades speed for another selected axis.
def cost (x : Nat) (axis : Bool) : Int :=
  match x, axis with
  | 0, false => 1 | 0, true => 10
  | 1, false => 10 | 1, true => 1
  | 2, _ => 0
  | 3, false => 1 | 3, true => 10
  | 4, _ => 20
  | _, _ => 30

def dom := pareto [false, true] cost
def allLive (_ : Nat) := true
example : compute ([] : List Nat) allLive dom = [] := by decide
example : compute [0,1,2] (fun _ => false) dom = [] := by decide
example : compute [0,1] allLive dom = [0,1] := by decide
example : compute [0,3] allLive dom = [0,3] := by decide
example : compute [0,0,3] allLive dom = [0,0,3] := by decide
example : compute [0,1,2] allLive dom = [2] := by decide
example : compute [0,1,4] allLive dom = [0,1] := by decide
example : compute [0,1,2] (fun x => x != 2) dom = [0,1] := by decide
-- Removing one of two dominators does not resurrect identity 4.
example : compute [0,1,4] (fun x => x != 0) dom = [1] := by decide
example : compute [0,1,4] (fun x => x == 4) dom = [4] := by decide
-- Pareto membership does not imply no regression against baseline 0.
example : 1 ∈ compute [0,1] allLive dom ∧ cost 1 false > cost 0 false := by decide
-- No-worse guard rejects tradeoff 1, preserves tie 3, then admits improving 2.
def guard (x : Nat) : Bool := [false,true].all (fun i => decide (cost x i ≤ cost 0 i))
example : compute [0,1,3] guard dom = [0,3] := by decide
example : compute [0,1,2,3] guard dom = [2] := by decide
-- Empty axis list makes every eligible identity a tie, not a strict winner.
example : compute [0,1,2] allLive (pareto ([] : List Bool) cost) = [0,1,2] := by decide
-- Frontier-only storage loses information needed for exact future retraction.
example : compute [0,1,2] allLive dom = compute [2] allLive dom ∧
    compute [0,1,2] (fun x => x != 2) dom ≠ compute [2] (fun x => x != 2) dom := by decide
end FrontierTests
