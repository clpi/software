namespace SoftwareIsComposable

structure Bounds where
  lo : Nat
  hi : Nat
deriving DecidableEq, Repr

structure SymbolProfile where
  id : Nat
  behaviors : List Nat
  costs : List Bounds
deriving DecidableEq, Repr

structure Release where
  symbols : List SymbolProfile
deriving DecidableEq, Repr

inductive Reason where
  | missingSymbol (symbol : Nat)
  | behaviorDropped (symbol behavior : Nat)
  | costRegressed (symbol axis : Nat)
  | axisMismatch (symbol : Nat)
  | invalidBounds (symbol : Nat)
deriving DecidableEq, Repr

inductive Verdict where
  | admitted
  | refused (reason : Reason)
deriving DecidableEq, Repr

structure Call where
  caller : Nat
  callee : Nat
  behavior : Nat
  expected : Nat
deriving DecidableEq, Repr

def InteractionClosed (moduleOf : Nat → Nat) (calls : List Call) : Prop :=
  ∀ c ∈ calls, moduleOf c.caller = moduleOf c.callee

def UniqueIds (r : Release) : Prop :=
  r.symbols.Pairwise fun a b => a.id ≠ b.id

structure SymbolCoverage (n : Nat) where
  observe : Fin n → Bool

end SoftwareIsComposable
