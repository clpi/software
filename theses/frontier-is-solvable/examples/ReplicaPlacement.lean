import Frontier

namespace ReplicaPlacement
open FrontierSolvable

-- Three client sites lie at 0, 2, 6 on a line. A mask selects hosted replicas.
structure Layout where
  west : Bool
  hub : Bool
  east : Bool
  deriving DecidableEq, Repr

def masks : List Layout := [false,true].flatMap fun w =>
  [false,true].flatMap fun h => [false,true].map fun e => ⟨w,h,e⟩

theorem every_layout (p : Layout) : p ∈ masks := by
  rcases p with ⟨a,b,c⟩
  cases a <;> cases b <;> cases c <;> decide

def sites (p : Layout) : List Nat :=
  (if p.west then [0] else []) ++ (if p.hub then [2] else []) ++ (if p.east then [6] else [])
def distance (x y : Nat) := x - y + (y - x)
def radius (p : Layout) :=
  ([0,2,6].map (fun client =>
    ((sites p).map (distance client)).foldl min 7)).foldl max 0
inductive Axis where | copies | distance
def axes := [Axis.copies, Axis.distance]
def cost (p : Layout) : Axis → Int
  | .copies => (sites p).length
  | .distance => radius p
def live (hubOnline : Bool) (p : Layout) := !(sites p).isEmpty && (hubOnline || !p.hub)
def dom := pareto axes cost
def plans (online : Bool) := compute masks (live online) dom
def result (online : Bool) := (plans online).map (fun p => (sites p, radius p))

-- Nondominance ranges over all physical placements, since all eight masks occur.
theorem frontier_for_all_layouts (online : Bool) (p : Layout) :
    p ∈ plans online ↔ live online p = true ∧
      ∀ q, live online q = true → dom q p = false := by
  rw [plans, compute_exact]
  simp [Frontier, every_layout]

theorem before_after :
    result true = [([2],4), ([2,6],2), ([0,6],2), ([0,2,6],0)] ∧
    result false = [([6],6), ([0],6), ([0,6],2)] := by decide

-- Simply deleting offline winners loses both currently optimal single-site fallbacks.
theorem winners_only_fails :
    ((plans true).filter (live false)).map sites = [[0,6]] := by decide

#eval (result true, result false)
#print axioms frontier_for_all_layouts
#print axioms before_after
#print axioms winners_only_fails
end ReplicaPlacement
