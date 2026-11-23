import Redundancy
namespace TestingRedundancy.Tests
open Qualification TestingRedundancy

-- Finite executable decision procedure, exact for the supplied model catalogue.
def redundantOn {M : Type} (models : List M) (e t : M → Bool) : Bool :=
  models.all (fun m => !e m || t m)

theorem redundantOn_correct {M : Type} (models : List M) (e t : M → Bool) :
    redundantOn models e t = true ↔
      ∀ m, m ∈ models → e m = true → t m = true := by
  simp only [redundantOn, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true]
  constructor
  · intro h m hm he
    rcases h m hm with no | yes
    · rw [he] at no
      cases no
    · exact yes
  · intro h m hm
    cases he : e m with
    | false => exact Or.inl rfl
    | true => exact Or.inr (h m hm he)

theorem exhaustive_catalogue_exact {M : Type} (models : List M)
    (complete : ∀ m, m ∈ models) (e t : M → Bool) :
    redundantOn models e t = true ↔ ∀ m, e m = true → t m = true := by
  rw [redundantOn_correct]
  exact ⟨fun h m => h m (complete m), fun h m _ => h m⟩

example : redundantOn [false, true] (fun b => b) (fun b => b) = true := by decide
example : redundantOn [false, true] (fun _ => true) (fun b => b) = false := by decide
-- Empty catalogue is only vacuously sufficient for its empty scope, not global.
example : redundantOn ([] : List Bool) (fun _ => true) (fun _ => false) = true := by decide
-- Duplicate models do not add distinguishing power to this set-based checker.
example : redundantOn [false, false] (fun _ => true) (fun b => !b) = true := by decide
example : redundantOn [false, true] (fun _ => true) (fun b => !b) = false := by decide
-- Same current evidence permits both models; a new manually specified assertion
-- distinguishes them. The assertion was not redundant even though the space is finite.
example : ¬ Entails (fun _ : Bool => True) (fun b => b = true) := by
  intro h
  have bad := h false trivial
  cases bad

example : ¬ ∃ infer : Unit → Bool, ∀ b : Bool, infer () = b := by
  exact observational_independence (fun _ : Bool => ()) id false true rfl (by decide)

-- Equal returned value does not qualify effects. Pair = (return, effect).
example : ¬ ∃ infer : Bool → Bool,
    ∀ m : Bool × Bool, infer m.1 = m.2 := by
  exact observational_independence Prod.fst Prod.snd
    (false, false) (false, true) rfl (by decide)

-- Run identity matters: a duplicate receipt has no new atom. A fresh observation
-- is not a duplicate just because its result equals an earlier result.
example : ∀ a : Nat, Derives (Join (fun n => n = 0) (fun n => n = 0))
    (fun _ _ => False) a ↔ Derives (fun n => n = 0) (fun _ _ => False) a := by
  exact singleton_duplicate _ _ 0 (Derives.root rfl)

example : ¬ Derives (fun n : Nat => n = 0) (fun _ _ => False) 1 := by
  intro h
  have wrong : (1 : Nat) = 0 := least (fun _ h => h)
    (fun _ _ h _ => False.elim h) 1 h
  cases wrong

-- Joint-premise hyperedge: both A and B are needed for C. No pairwise
-- incidence edge is permission to derive C from A alone.
inductive Fact where | a | b | c deriving DecidableEq
open Fact

def JointRule (ps : List Fact) (out : Fact) : Prop := ps = [a, b] ∧ out = c

example : Derives (fun f => f = a ∨ f = b) JointRule c := by
  apply Derives.step (ps := [a, b]) ⟨rfl, rfl⟩
  intro p hp
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
  exact Derives.root hp

example : ¬ Derives (fun f => f = a) JointRule c := by
  intro h
  have hc : c = a := least (fun _ h => h) (by
    intro ps out rule hp
    rcases rule with ⟨rfl, rfl⟩
    have bad : b = a := hp b (by simp)
    cases bad) c h
  cases hc

-- Two polarities are independent supports: deriving a positive obligation does
-- not permit throwing away a newly supplied negative observation.
example : ¬ Covered (fun b : Bool => b = true) (fun _ _ => False)
    (fun b => b = false) := by
  intro h
  have hd := h false rfl
  have bad : false = true := least (fun _ h => h)
    (fun _ _ h _ => False.elim h) false hd
  cases bad

-- An exact count threshold is not set idempotence on equal outcome values.
example : (([true, true] : List Bool).length ≥ 2) ∧
    ¬ (([true] : List Bool).length ≥ 2) := by decide

-- Withdrawal removes the old derivation, so redundancy must be rechecked at
-- the current snapshot, not inherited from a historical certificate.
example : ¬ Derives (liveRoots (fun _ : Unit => True) (fun _ => True))
    (fun _ _ => False) () := by
  intro h
  exact least (fun _ h => h.2 trivial) (fun _ _ h _ => h) () h

#print axioms redundantOn_correct
#print axioms exhaustive_catalogue_exact
end TestingRedundancy.Tests
