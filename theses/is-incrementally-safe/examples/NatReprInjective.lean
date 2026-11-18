import SoftwareIsIncrementallySafe
import DependencyModules

open SoftwareIsComposable
open AuditDependencyModules.Legacy

example (a b : Nat) (h : Nat.repr a = Nat.repr b) : a = b :=
  Nat.repr_injective h

example (calls : List (Nat × Nat)) (seeds : List Nat) (s : Nat) :
    StringCone (calls.map fun c => (Nat.repr c.1, Nat.repr c.2)) (seeds.map Nat.repr)
        (Nat.repr s) ↔
      InClosure calls seeds s :=
  stringCone_iff_inClosure_repr calls seeds s

example (calls : List (Nat × Nat)) (seeds : List Nat) (s : Nat) :
    StringCone (calls.map fun c => (Nat.repr c.1, Nat.repr c.2)) (seeds.map Nat.repr)
        (Nat.repr s) ↔
      HypergraphIncremental.Affected (hyper [] calls) (hyper seeds calls) s :=
  stringCone_iff_affected_repr calls seeds s
