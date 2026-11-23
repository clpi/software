import SoftwareDoesntNeedReview.Certifier

namespace SoftwareDoesntNeedReview

def diffSyms (base cand : Release) : List Sym :=
  cand.cells.foldl (fun acc c =>
    if behaviorAt base c.symbol c.axis != behaviorAt cand c.symbol c.axis then
      c.symbol :: acc
    else
      acc) []

structure Sight where
  diff : List Sym
  facts : Facts
deriving DecidableEq, Repr

def sightOf (C : Certifier) (base cand : Release) : Sight :=
  { diff := diffSyms base cand
    facts := factsOf C cand }

abbrev Reviewer := Sight → Bool

def FactorsThrough (r : Reviewer) : Prop :=
  ∀ s1 s2 : Sight, s1.facts = s2.facts → r s1 = r s2

def Respects (r : Reviewer) (C : Certifier) (base : Release) : Prop :=
  ∀ R, r (sightOf C base R) = true → (factsOf C R).refusals = []

def certBit (f : Facts) : Bool :=
  f.refusals.isEmpty

def alwaysReject : Reviewer := fun _ => false

def alwaysApprove : Reviewer := fun _ => true

end SoftwareDoesntNeedReview
