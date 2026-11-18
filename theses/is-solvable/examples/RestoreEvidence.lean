import WitnessExecutable

namespace RestoreEvidence
open WitnessExecutable ExecutableClosure

inductive Fact where
  | snapshot | checksum | replay | intact | restorable
  deriving DecidableEq, Repr
open Fact

def domain := [snapshot, checksum, replay, intact, restorable]
def rules : List (List Fact × Fact) :=
  [([snapshot, checksum], intact), ([intact, replay], restorable)]
def old : Batch Fact := ⟨[snapshot], rules⟩

-- Checksum only (3 units), isolated replay (5), or a combined lab run (6).
-- All costs are fixture inputs. A plan buys each of the three at most once.
structure Plan where
  hashOnly : Bool
  replayOnly : Bool
  combined : Bool

def observations (p : Plan) : Batch Fact :=
  ⟨(if p.hashOnly then [checksum] else []) ++ (if p.replayOnly then [replay] else []) ++
    (if p.combined then [checksum, replay] else []), []⟩

def cost (p : Plan) := (if p.hashOnly then 3 else 0) + (if p.replayOnly then 5 else 0) +
    (if p.combined then 6 else 0)

def facts (b : Batch Fact) := checkedClose domain b.roots b.edges
def ready (p : Plan) := ((facts (append old (observations p))).map (·.contains restorable)) == some true
def separate : Plan := ⟨true,true,false⟩
def joint : Plan := ⟨false,false,true⟩

theorem minimum (p : Plan) : ready p = true → cost joint ≤ cost p := by
  rcases p with ⟨a,b,c⟩
  cases a <;> cases b <;> cases c <;> decide

theorem before_after : ready separate = true ∧ ready joint = true ∧
    cost separate = 8 ∧ cost joint = 6 := by decide

-- Pooling already-computed support loses both mixed-premise conclusions.
theorem reclosure_matters : facts old = some [snapshot] ∧
    facts (observations joint) = some [checksum,replay] ∧
    facts (append old (observations joint)) = some domain ∧
    ready ⟨true,false,false⟩ = false := by decide

#eval (cost separate, cost joint, facts (append old (observations joint)))
#print axioms minimum
#print axioms before_after
#print axioms reclosure_matters
end RestoreEvidence
