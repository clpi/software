/-
  Standing controls for the choral checking theorems. Each control
  is a concrete two-module development on which one premise of the
  main theorems fails and the conclusion fails with it: the
  premises are load-bearing, not decoration.
-/

import Choral

open Choral

/-- A two-module type for the controls. -/
inductive Two where
  | a : Two
  | b : Two
deriving DecidableEq

namespace Controls

/-- First development: `b` depends on `a`; both modules pass their
    own local check. -/
def ownA : Two → Bool := fun _ => true

def depsA : Two → List Two
  | .a => []
  | .b => [.a]

def rankA : Two → Nat
  | .a => 0
  | .b => 1

theorem hrankA : ∀ m d, d ∈ depsA m → rankA d < rankA m := by
  intro m d h
  cases m with
  | a => simp [depsA] at h
  | b =>
      cases d with
      | a => decide
      | b => simp [depsA] at h

/-- Control one: the boundary premise is load-bearing. The whole
    check passes `b`, since `a` passes and `b` passes. The cone
    containing only `b`, read against a boundary that reports `a`
    as failed, fails `b`. A cone verdict is worth exactly what its
    boundary is worth. -/
theorem boundarymatters :
    cone ownA depsA rankA [Two.b] (fun _ => false) Two.b
      ≠ whole ownA depsA rankA Two.b := by
  have h1 : cone ownA depsA rankA [Two.b] (fun _ => false) Two.b = false := rfl
  have h2 : whole ownA depsA rankA Two.b = true := rfl
  rw [h1, h2]
  exact Bool.false_ne_true

/-- Second development: no dependencies; `a` passes, `b` fails. -/
def ownB : Two → Bool
  | .a => true
  | .b => false

def depsB : Two → List Two := fun _ => []

def rankB : Two → Nat := fun _ => 0

theorem hrankB : ∀ m d, d ∈ depsB m → rankB d < rankB m := by
  intro m d h
  simp [depsB] at h

/-- Control two: the coverage premise is load-bearing. With the
    honest boundary (the whole check itself), the joined verdict
    over the cones `[a]`, `[]`, `[]` holds — the only covered
    module passes — while the whole verdict fails at the uncovered
    module `b`. A join over a family that does not cover the
    development certifies a development that does not pass. -/
theorem covermatters :
    (∀ C ∈ ([[Two.a], [], []] : List (List Two)), ∀ m ∈ C,
        cone ownB depsB rankB C (whole ownB depsB rankB) m = true)
    ∧ ¬ (∀ m, whole ownB depsB rankB m = true) := by
  constructor
  · intro C hC m hm
    have hC3 : C = [Two.a] ∨ C = [] ∨ C = [] := by simpa using hC
    rcases hC3 with rfl | rfl | rfl
    · have hma : m = Two.a := by simpa using hm
      subst hma
      rfl
    · simp at hm
    · simp at hm
  · intro h
    have hb := h Two.b
    have hbf : whole ownB depsB rankB Two.b = false := rfl
    rw [hbf] at hb
    exact Bool.noConfusion hb

end Controls
