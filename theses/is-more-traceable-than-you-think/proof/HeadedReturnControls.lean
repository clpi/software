/-
  Adversarial controls for HeadedReturn. Controls for dropping the
  headed and the closed conditions already stand in ReturnControls
  (head_without_derivation, derivation_without_head); the first two
  theorems below tie them to the named conditions. The rest attack
  what ReturnControls does not: the witnessed hypothesis, the
  grounded condition, uniqueness under all three conditions, and
  the carry-over reading.
-/

import Controls
import ReturnControls
import HeadedReturn

namespace HeadedReturnControls

open Traceability HeadedReturn

/-- The node-only lifting of ReturnControls is not headed, so its
    standing counterexample is the control for dropping `Headed`. -/
theorem nodeOnly_not_headed : ¬ Headed ReturnControls.nodeOnly := by
  intro h
  rcases h () false (by decide) with ⟨d, hd, _⟩
  exact Bool.false_ne_true hd

/-- The edge-only lifting of ReturnControls is not closed, so its
    standing counterexample is the control for dropping `Closed`. -/
theorem edgeOnly_not_closed : ¬ Closed ReturnControls.edgeOnly := by
  intro h
  have h1 := h () ReturnControls.noPremises rfl
  exact Bool.false_ne_true h1

open Controls

/- Each control attacks the provable return of a
   witnessed head, `returns_headed` and its companions, by removing
   one hypothesis or by asking for more than is proven, and shows
   on concrete data that the stronger claim fails. -/

/-- A headed contribution assignment for the return controls:
    each event contributes its own node, and every derivation
    whose head is that node, whatever its premise set. -/
def headlift (e : Nat) : Graph Nat :=
  ⟨fun n => decide (n = e), fun d => decide (d.head = e)⟩

/-- The return controls' assignment is headed, so the headed
    hypothesis of `returns_headed` is satisfiable on real data. -/
theorem headlift_headed : Headed headlift := by
  intro e n hn
  simp [headlift] at hn
  exact ⟨⟨fun _ => false, n⟩, by simp [headlift, hn], rfl⟩

/-- The return controls' assignment is closed. -/
theorem headlift_closed : Closed headlift := by
  intro e d hd
  simpa [headlift] using hd

/-- Non-vacuity of the return: on a two-event stream, the
    witnessed node one returns to a present derivation headed at
    one, contributed by an event of the stream. -/
theorem headlift_returns :
    ∃ d, (fold headlift [0, 1]).edges d = true ∧ d.head = 1 ∧
      ∃ e, e ∈ [0, 1] ∧ (headlift e).nodes 1 = true ∧
        (headlift e).edges d = true :=
  returns_headed headlift headlift_headed
    ((fold_nodes headlift).mpr ⟨1, by simp, by simp [headlift]⟩)

/-- Control for the witnessed hypothesis: without it, the return
    fails even under a headed assignment. Node five is not
    witnessed in the fold of the stream holding event zero, and
    no present derivation is headed at five. -/
theorem witnessed_needed :
    ¬ (∀ n : Nat, ∃ d, (fold headlift [0]).edges d = true ∧ d.head = n) := by
  intro h
  rcases h 5 with ⟨d, hd, hh⟩
  rcases (fold_edges headlift).mp hd with ⟨e, he, hce⟩
  simp at he
  subst he
  simp [headlift] at hce
  omega

/-- Control for the grounded hypothesis: under the headed and
    closed assignment, a present derivation can name a premise
    the fold never witnessed. The derivation headed at zero with
    every premise present is in the fold of the stream holding
    event zero, and its premise node one is not witnessed. -/
theorem grounded_needed :
    ¬ (∀ (d : Derivation Nat) (m : Nat), (fold headlift [0]).edges d = true →
      d.premises m = true → (fold headlift [0]).nodes m = true) := by
  intro h
  have hp := h ⟨fun _ => true, 0⟩ 1
    ((fold_edges headlift).mpr ⟨0, by simp, by simp [headlift]⟩) rfl
  rcases (fold_nodes headlift).mp hp with ⟨e, he, hce⟩
  simp at he
  subst he
  simp [headlift] at hce

/-- Two derivations over a two-node type, sharing head `true`:
    one with every premise present, one with none. -/
def fullB : Derivation Bool := ⟨fun _ => true, true⟩

/-- The second derivation over the two-node type. -/
def noB : Derivation Bool := ⟨fun _ => false, true⟩

/-- A split contribution assignment over the two-node type: both
    nodes witnessed by every event; event zero contributes the
    derivations with every premise present, every other event the
    derivations with no premise present, at either head. -/
def splitlift (e : Nat) : Graph Bool :=
  ⟨fun _ => true, fun d => (d.premises true == decide (e = 0)) &&
    (d.premises false == decide (e = 0))⟩

/-- The split assignment is headed. -/
theorem splitlift_headed : Headed splitlift := by
  intro e n _
  exact ⟨⟨fun _ => decide (e = 0), n⟩, by simp [splitlift], rfl⟩

/-- The split assignment is closed. -/
theorem splitlift_closed : Closed splitlift := by
  intro e d _
  rfl

/-- The split assignment is grounded. -/
theorem splitlift_grounded : Grounded splitlift := by
  intro e d m _ _
  rfl

/-- Each event of the split assignment contributes at most one
    derivation at each head: two derivations one event contributes
    with the same head are equal. So no single event is ambiguous
    about the premise set of a head. -/
theorem splitlift_functional (e : Nat) (d d' : Derivation Bool)
    (hd : (splitlift e).edges d = true)
    (hd' : (splitlift e).edges d' = true)
    (hh : d.head = d'.head) : d = d' := by
  cases d with
  | mk p h =>
    cases d' with
    | mk p' h' =>
      simp [splitlift] at hd hd' hh
      have hp : p = p' := by
        funext b
        cases b <;> simp_all
      rw [hp, hh]

/-- The two derivations of the split control are different. -/
theorem fullB_ne_noB : fullB ≠ noB := by
  intro h
  have h1 := congrArg (fun d => d.premises true) h
  simp [fullB, noB] at h1

/-- Control for exactness of the returned premise set: even when
    the assignment is headed, closed and grounded, and every event
    contributes at most one derivation at each head, the fold of a
    stream can hold two different present derivations with the
    same head. The witnessed head `true` returns to both, so the
    return does not single out one premise set. -/
theorem return_not_unique :
    (fold splitlift [0, 1]).edges fullB = true ∧
      (fold splitlift [0, 1]).edges noB = true ∧
      fullB.head = noB.head ∧ fullB ≠ noB :=
  ⟨(fold_edges splitlift).mpr ⟨0, by simp, by decide⟩,
    (fold_edges splitlift).mpr ⟨1, by simp, by decide⟩,
    rfl, fullB_ne_noB⟩

/-- A property of a hypergraph: at most one node is witnessed. -/
def atmostone (g : Graph Nat) : Prop :=
  ∀ n m, g.nodes n = true → g.nodes m = true → n = m

/-- The property holds for the fold of every one-event stream
    under the own-node assignment. -/
theorem atmostone_singletons : ∀ e, atmostone (fold ownlift [e]) := by
  intro e n m hn hm
  rcases (fold_nodes ownlift).mp hn with ⟨a, ha, hna⟩
  rcases (fold_nodes ownlift).mp hm with ⟨b, hb, hmb⟩
  simp at ha hb
  simp [ownlift] at hna hmb
  omega

/-- Control for the closure reading of `returns_headed`: a property
    that holds at every one-event stream need not carry over to a
    longer stream. So the carry-over of the return from one event
    to every stream, which `headed_iff_singleton` shows is all
    `returns_headed` adds, is a property the fold has to earn. -/
theorem atmostone_not_lifted : ¬ atmostone (fold ownlift [0, 1]) := by
  intro h
  have h1 := h 0 1 ((fold_nodes ownlift).mpr ⟨0, by simp, by simp [ownlift]⟩)
    ((fold_nodes ownlift).mpr ⟨1, by simp, by simp [ownlift]⟩)
  omega

end HeadedReturnControls
