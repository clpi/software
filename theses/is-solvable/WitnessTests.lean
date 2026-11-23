import WitnessExecutable
namespace WitnessTests
open Hyperlattice WitnessExecutable ExecutableClosure

def u : List Nat := [0,1,2,3,4]
def old : Batch Nat := ⟨[0], [([0,1],2),([2],3)]⟩
def fresh : Batch Nat := ⟨[1], []⟩
def run (b : Batch Nat) := close u b.roots b.edges
-- Cross-premise synergy: 2 and 3 are not in either individual closure.
#guard run old == [0]
#guard run fresh == [1]
#guard run (append old fresh) == [0,1,2,3]
#guard !(run old ++ run fresh).contains 2
#guard interaction old 0 1
#guard incidence old ([0,1],2) 1
#guard !(incidence old ([0,1],2) 4)
-- Roots AND rules arrive incrementally: a rule-only append can be novel.
#guard run (append (⟨[0,1], []⟩ : Batch Nat) (⟨[], [([0,1],2)]⟩ : Batch Nat)) == [0,1,2]
-- Duplicate and already-derived support do not expand semantic resolution.
#guard run (append old old) == run old
#guard run (append (append old fresh) (⟨[2], []⟩ : Batch Nat)) == run (append old fresh)
-- Per-axis vector: direct observation [0,1], composite qualification [2,3].
def axes : Bool → List Nat | false => [0,1] | true => [2,3]
#guard resolution axes (classify u old) false == 1
#guard resolution axes (classify u old) true == 0
#guard resolution axes (classify u (append old fresh)) false == 2
#guard resolution axes (classify u (append old fresh)) true == 2
-- Catalogue size 2 -> 16 is this example, not a strict-growth assumption.
#guard (configurations u old).length == 2
#guard (configurations u (append old fresh)).length == 16
#guard (configurations u (append old old)).length == 2
-- Gate is an executable filter, and may narrow a previously admitted set.
def gateGood (xs : List Nat) := xs.contains 3 && !(xs.contains 4)
#guard (qualified u (append old fresh) gateGood).length == 8
-- 4 is negative support: history grows; favorable status changes to conflict.
def negative : Batch Nat := ⟨[4], []⟩
#guard color (classify u (append old fresh) 3) (classify u (append old fresh) 4) == 1
#guard color (classify u (append (append old fresh) negative) 3)
  (classify u (append (append old fresh) negative) 4) == 3
-- Historical origin plus every premise/transfer must remain live.
def cyc : Batch Nat := ⟨[0], [([0],1),([1],0),([1],2)]⟩
#guard run cyc == [0,1,2]
#guard run (project cyc (fun a => a == 0) (fun _ => false)) == []
#guard run cyc == [0,1,2]
-- Independent live support preserves a conclusion after the other route is withdrawn.
def twoOrigins : Batch Nat := ⟨[0,4], [([0],2),([4],2)]⟩
#guard run (project twoOrigins (fun a => a == 0) (fun _ => false)) == [2,4]
-- Removing a transfer retracts its downstream consequence.
#guard run (project old (fun _ => false) (fun _ => true)) == [0]
-- Malformed domain admission is rejected, not vacuously qualified.
#guard checkedClose [0] [1] [] == none
#guard checkedClose [0] [] [([],1)] == none
-- No unintended inference from solitary cycles.
#guard close [0,1] [] [([0],1),([1],0)] == []
-- Qualification can be empty, even with a nonempty exact catalogue.
#guard qualified u old (fun _ => false) == []
end WitnessTests
