import Std

namespace RangeLedger.LinearProvenance
inductive Expr where | read (endpoint : Nat) | add (a b : Expr) | neg (a : Expr)
def eval (p : Nat → Int) : Expr → Int
  | .read i => p i
  | .add a b => eval p a + eval p b
  | .neg a => -(eval p a)
def coeff (i : Nat) : Expr → Int
  | .read j => if i = j then 1 else 0
  | .add a b => coeff i a + coeff i b
  | .neg a => -(coeff i a)
def bump (p : Nat → Int) (i : Nat) (v : Int) := fun j => p j + (if i = j then v else 0)
theorem derivative (p : Nat → Int) (i : Nat) (v : Int) (e : Expr) :
    eval (bump p i v) e = eval p e + coeff i e * v := by
  induction e with
  | read j => by_cases h : i=j <;> simp [eval,bump,coeff,h]
  | add a b ha hb => simp only [eval,coeff,ha,hb,Int.add_mul]; omega
  | neg a ha => simp only [eval,coeff,ha,Int.neg_mul]; omega

open Expr
def interval (a b : Nat) := add (.read b) (neg (.read a))
def source := add (add (interval 0 3072) (neg (interval 1024 3072))) (interval 1024 4096)
def folded := interval 0 4096
theorem normalize (p : Nat → Int) : eval p source = eval p folded := by
  simp [source,folded,interval,eval]; omega

-- Two distinct endpoints suffice for a direct-potential venue. Each influences
-- the result, so a nonadaptive direct read set recovering the query must include both.
theorem necessary (ks : List Nat) (decodes : ∀ p q : Nat → Int,
    (∀ k ∈ ks, p k = q k) → eval p source = eval q source) (j : Nat) (hj : j = 0 ∨ j = 4096) :
    j ∈ ks := by
  apply Classical.byContradiction; intro absent
  let spike : Nat → Int := fun k => if k = j then 1 else 0
  have eq := decodes (fun _ => 0) spike (fun k hk => by
    have ne : k ≠ j := fun e => absent (e ▸ hk)
    simp [spike,ne])
  rw [normalize,normalize] at eq
  rcases hj with rfl | rfl <;> simp [folded,interval,eval,spike] at eq
theorem coefficients : [0,1024,3072,4096].map (fun k => coeff k source) = [-1,0,0,1] := by decide
#print axioms derivative
#print axioms normalize
#print axioms necessary
#print axioms coefficients
end RangeLedger.LinearProvenance
