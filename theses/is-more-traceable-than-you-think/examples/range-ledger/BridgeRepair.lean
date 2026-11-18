import Std

namespace RangeLedger.BridgeRepair

inductive Wire where | ab | ac | ad | bc | bd | cd deriving DecidableEq, Repr
open Wire
def ends : Wire → Fin 4 × Fin 4
  | ab => (0,1) | ac => (0,2) | ad => (0,3)
  | bc => (1,2) | bd => (1,3) | cd => (2,3)

-- The four internal receipt components have independent unknown potential offsets.
def value (p : Fin 4 → Int) (w : Wire) := p (ends w).2 - p (ends w).1
def bit (mask : Nat) (i : Fin 4) : Int := ((mask / 2^i.val) % 2 : Nat)
def blind (ws : List Wire) := (List.range 16).find? fun m =>
  decide (0 < m ∧ m < 15) && ws.all (fun w => value (bit m) w == 0)

theorem returned_cut (ws : List Wire) (m : Nat) (found : blind ws = some m) :
    0 < m ∧ m < 15 ∧ ∀ w ∈ ws, value (bit m) w = 0 := by
  have yes := List.find?_some found
  simpa [Bool.and_eq_true,List.all_eq_true,and_assoc] using yes

theorem cut_distinguishes (m : Fin 16) (nontrivial : 0 < m.val ∧ m.val < 15) :
    ∃ i j : Fin 4, bit m.val i ≠ bit m.val j := by
  have witness : ([0,1,2,3] : List (Fin 4)).any (fun i => bit m.val i != bit m.val 0) = true := by
    revert nontrivial m; decide
  obtain ⟨i,_,hi⟩ := List.any_eq_true.mp witness
  exact ⟨i,0,by simpa using hi⟩

theorem two_never_enough (ws : List Wire) (cap : ws.length ≤ 2) : (blind ws).isSome = true := by
  rcases ws with _ | ⟨a,tail⟩
  · decide
  rcases tail with _ | ⟨b,tail⟩
  · cases a <;> decide
  rcases tail with _ | ⟨c,tail⟩
  · cases a <;> cases b <;> decide
  · simp at cap

theorem ambiguity (ws : List Wire) (cap : ws.length ≤ 2) :
    ∃ p : Fin 4 → Int, (∀ w ∈ ws, value p w = 0) ∧ ∃ i j, p i ≠ p j := by
  have someCut := two_never_enough ws cap
  cases found : blind ws with
  | none => simp [found] at someCut
  | some m =>
    obtain ⟨lo,hi,same⟩ := returned_cut ws m found
    exact ⟨bit m,same,cut_distinguishes ⟨m,by omega⟩ ⟨lo,hi⟩⟩

def recover (x y z : Int) (i : Fin 4) : Int := [0,x,x+y,x+y+z].getD i.val 0
theorem three_suffice (p : Fin 4 → Int) (i : Fin 4) :
    recover (value p ab) (value p bc) (value p cd) i = p i - p 0 := by
  have cases4 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases cases4 with rfl | rfl | rfl | rfl
  · change 0 = p 0 - p 0; omega
  · rfl
  · change (p 1 - p 0) + (p 2 - p 1) = p 2 - p 0; omega
  · change (p 1 - p 0) + (p 2 - p 1) + (p 3 - p 2) = p 3 - p 0; omega
theorem bad_three : (blind [ab,ac,bc]).isSome = true ∧ blind [ab,bc,cd] = none := by decide
#eval (blind [ab,ac,bc],blind [ab,bc,cd])
#print axioms returned_cut
#print axioms cut_distinguishes
#print axioms two_never_enough
#print axioms ambiguity
#print axioms three_suffice
#print axioms bad_three
end RangeLedger.BridgeRepair
