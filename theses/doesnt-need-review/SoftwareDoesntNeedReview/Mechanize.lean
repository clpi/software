import SoftwareDoesntNeedReview.Certifier

namespace SoftwareDoesntNeedReview

namespace Mechanize

inductive Criterion where
  | profile (symbol : Sym) (axis : Ax)
  | semantic (name : String)
  | approx (name : String) (symbol : Sym) (axis : Ax) (gap : String)
deriving DecidableEq, Repr

inductive Outcome where
  | axis (symbol : Sym) (axis : Ax)
  | premise (name : String)
  | approx (name : String) (symbol : Sym) (axis : Ax) (gap : String)
deriving DecidableEq, Repr

def isTotalAxis : Outcome → Bool
  | Outcome.axis _ _ => true
  | _ => false

def dispose : Criterion → Outcome
  | Criterion.profile s a => Outcome.axis s a
  | Criterion.semantic n => Outcome.premise n
  | Criterion.approx n s a g => Outcome.approx n s a g

theorem profile_becomes_axis (s : Sym) (a : Ax) :
    dispose (Criterion.profile s a) = Outcome.axis s a := rfl

theorem semantic_not_total_axis (n : String) :
    isTotalAxis (dispose (Criterion.semantic n)) = false := rfl

theorem semantic_stays_premise (n : String) :
    dispose (Criterion.semantic n) = Outcome.premise n := rfl

def gapNamed : Outcome → Bool
  | Outcome.approx _ _ _ g => !(g == "")
  | _ => false

theorem approx_not_total_axis (n : String) (s : Sym) (a : Ax) (g : String) :
    isTotalAxis (dispose (Criterion.approx n s a g)) = false := rfl

theorem approx_keeps_gap (n : String) (s : Sym) (a : Ax) (g : String) :
    dispose (Criterion.approx n s a g) = Outcome.approx n s a g := rfl

theorem approx_gap_named (n : String) (s : Sym) (a : Ax) (g : String)
    (h : (g == "") = false) :
    gapNamed (dispose (Criterion.approx n s a g)) = true := by
  simp [gapNamed, dispose, h]

structure Program where
  identity : Nat

end Mechanize

end SoftwareDoesntNeedReview
