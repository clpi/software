/-
  Standing controls for the persistence minimality model.

  Each control is a proved negation over concrete numbers:
  a load-bearing condition of the model is removed or
  varied, and the failure is exhibited exactly. The controls
  stand in the tree permanently; a change that breaks one
  has broken the condition it guards.
-/

import Core

namespace Persistence

/-- No derivation from the empty store through a single
    recorded edge whose premise list is nonempty: the only
    edge demands a premise, the store supplies none, and
    induction on the derivation closes every case. The
    premise element named in the statement is the witness
    the step case is killed with. -/
theorem noderiv (ps : List Nat) (c q : Nat) (hq : q ∈ ps) :
    ∀ x, ¬ Deriv [(ps, c)] [] x := by
  intro x h
  induction h with
  | base hmem => simp at hmem
  | step hedge hps ih =>
    simp at hedge
    obtain ⟨rfl, rfl⟩ := hedge
    exact ih q hq

/-- The constant axis of the first control: every choice
    costs the same. -/
def aone : Nat → Nat → Nat := fun _ _ => 4

/-- The discriminating axis of the first control: choice
    zero costs seven, every other choice costs two. -/
def atwo : Nat → Nat → Nat :=
  fun _ c => if c = 0 then 7 else 2

/-- Control one, axis relativity: the representation zero
    is minimum under the constant axis alone, and stops
    being minimum once the discriminating axis is named,
    because on the full axis list the representation one
    dominates it. Minimality is relative to the contract's
    axis list, never absolute. -/
theorem controlone :
    Minimal [aone] [10] [[0], [1]] [0]
      ∧ ¬ Minimal [aone, atwo] [10] [[0], [1]] [0] := by
  constructor
  · refine ⟨by decide, ?_⟩
    intro s hs hdom
    obtain ⟨a, ha, hlt⟩ := hdom.2
    have haa : a = aone := by simpa using ha
    subst haa
    have hs' : s = [0] ∨ s = [1] := by simpa using hs
    cases hs' with
    | inl h =>
      subst h
      exact Nat.lt_irrefl _ hlt
    | inr h =>
      subst h
      exact absurd hlt (by decide)
  · intro hmin
    apply hmin.2 [1] (by decide)
    constructor
    · intro a ha
      have ha' : a = aone ∨ a = atwo := by simpa using ha
      cases ha' with
      | inl h =>
        subst h
        exact (by decide)
      | inr h =>
        subst h
        exact (by decide)
    · exact ⟨atwo, by simp, by decide⟩

/-- Control two, premise outside the closure: a recorded
    edge whose premise is not derivable does not make its
    conclusion derivable. Recording an edge is not enough;
    its premise cone must reach the store. -/
theorem controltwo : ¬ Deriv [([7], 9)] [] 9 :=
  noderiv [7] 9 7 (by decide) 9

/-- Control three, the lost version: from the empty store
    the version twenty is not readable through the recorded
    edge, because its premise ten is gone; with the premise
    kept in the store the same version is readable, by the
    kept-premise fact of the core. Naive per-version
    compression that drops the shared premise loses a
    still-readable version. -/
theorem controlthree :
    ¬ Readable [([10], 20)] [] [20]
      ∧ Readable [([10], 20)] [10] [20] := by
  constructor
  · intro hread
    exact noderiv [10] 20 10 (by decide) 20 (hread 20 (by decide))
  · exact kept

/-- The first tradeoff axis: part one prefers choice zero,
    part two prefers choice one. -/
def axone : Nat → Nat → Nat :=
  fun p c => if p = 1 then (if c = 0 then 5 else 8)
    else if p = 2 then (if c = 0 then 5 else 2) else 0

/-- The second tradeoff axis: part one prefers choice one,
    part two prefers choice zero. -/
def axtwo : Nat → Nat → Nat :=
  fun p c => if p = 1 then (if c = 0 then 5 else 2)
    else if p = 2 then (if c = 0 then 5 else 7) else 0

/-- Control four, the cross-part tradeoff: choice zero is
    minimum for part one alone and for part two alone, yet
    in the composed datum the appended part minima are
    dominated by the cross-part tradeoff choice, which loses
    on the first axis of part one and wins it back on the
    second axis of part two. Part minima do not compose;
    the whole must be minimized as a whole, or the tradeoff
    recorded as an interaction. -/
theorem controlfour :
    Minimal [axone, axtwo] [1] [[0], [1]] [0]
      ∧ Minimal [axone, axtwo] [2] [[0], [1]] [0]
      ∧ Dominates [axone, axtwo] [1, 2] [1, 1] [0, 0] := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    intro s hs hdom
    have hs' : s = [0] ∨ s = [1] := by simpa using hs
    cases hs' with
    | inl h =>
      subst h
      exact domirr hdom
    | inr h =>
      subst h
      have hle := hdom.1 axone (by simp)
      exact absurd hle (by decide)
  · refine ⟨by decide, ?_⟩
    intro s hs hdom
    have hs' : s = [0] ∨ s = [1] := by simpa using hs
    cases hs' with
    | inl h =>
      subst h
      exact domirr hdom
    | inr h =>
      subst h
      have hle := hdom.1 axtwo (by simp)
      exact absurd hle (by decide)
  · constructor
    · intro a ha
      have ha' : a = axone ∨ a = axtwo := by simpa using ha
      cases ha' with
      | inl h =>
        subst h
        exact (by decide)
      | inr h =>
        subst h
        exact (by decide)
    · exact ⟨axtwo, by simp, by decide⟩

#print axioms noderiv
#print axioms controlone
#print axioms controltwo
#print axioms controlthree
#print axioms controlfour

end Persistence
