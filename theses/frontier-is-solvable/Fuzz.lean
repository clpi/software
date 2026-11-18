namespace Fuzz

structure Atom where
  weight : Nat
  gain : Nat
  deriving DecidableEq, Repr

def expect (atoms : List Atom) : Nat :=
  atoms.foldl (fun acc atom => acc + atom.weight * atom.gain) 0

theorem shift (base : Nat) (atoms : List Atom) :
    List.foldl (fun acc item => acc + item.weight * item.gain) base atoms =
      base + List.foldl (fun acc item => acc + item.weight * item.gain) 0 atoms := by
  induction atoms generalizing base with
  | nil => simp
  | cons head tail ih =>
    simp only [List.foldl_cons, Nat.zero_add]
    rw [ih (base + head.weight * head.gain), ih (head.weight * head.gain)]
    omega

theorem add (atom : Atom) (atoms : List Atom) :
    expect (atom :: atoms) = atom.weight * atom.gain + expect atoms := by
  simp only [expect, List.foldl_cons, Nat.zero_add]
  exact shift (atom.weight * atom.gain) atoms

end Fuzz
