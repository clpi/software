/-
  Witnessed-head return under per-event conditions on the lifting.

  The generic model lets an event record a node without any
  derivation, or a derivation without its head (ReturnControls),
  so a witnessed head alone returns nothing. This module names the
  per-event conditions under which it does, proves the return for
  every lifting that meets them, and shows that the concrete
  recorder of Traceability is one such lifting. No hypothesis here
  names the fold: each condition is about one event at a time.
-/

import Traceability

namespace HeadedReturn

open Traceability

/-- A contribution assignment is headed when every node an event
    contributes is the head of some derivation that the same event
    contributes. This is a condition on one event at a time; it
    names no stream. -/
def Headed {Node Ev : Type} (lift : Ev → Graph Node) : Prop :=
  ∀ e n, (lift e).nodes n = true →
    ∃ d, (lift e).edges d = true ∧ d.head = n

/-- A contribution assignment is closed when every derivation an
    event contributes has its head among the nodes the same event
    contributes. A condition on one event at a time. -/
def Closed {Node Ev : Type} (lift : Ev → Graph Node) : Prop :=
  ∀ e d, (lift e).edges d = true → (lift e).nodes d.head = true

/-- A contribution assignment is grounded when every premise of
    every derivation an event contributes is among the nodes the
    same event contributes. A condition on one event at a time. -/
def Grounded {Node Ev : Type} (lift : Ev → Graph Node) : Prop :=
  ∀ e d m, (lift e).edges d = true → d.premises m = true →
    (lift e).nodes m = true

/-- **Provable return of a witnessed head, generic form.** Under a headed
    contribution assignment, every node witnessed in the folded
    hypergraph returns to a derivation present in the folded
    hypergraph whose head it is, and one event of the stream
    contributes both the node and that derivation. The
    contribution is derived from the fold, not assumed: the
    witnessed hypothesis is read by the proof term, through the
    node face, and the derivation face is reached from it. -/
theorem returns_headed {Node Ev : Type} (lift : Ev → Graph Node)
    (headed : Headed lift) {l : List Ev} {n : Node}
    (witnessed : (fold lift l).nodes n = true) :
    ∃ d, (fold lift l).edges d = true ∧ d.head = n ∧
      ∃ e, e ∈ l ∧ (lift e).nodes n = true ∧ (lift e).edges d = true := by
  rcases (fold_nodes lift).mp witnessed with ⟨e, he, hn⟩
  rcases headed e n hn with ⟨d, hd, hhead⟩
  exact ⟨d, (fold_edges lift).mpr ⟨e, he, hd⟩, hhead, e, he, hn, hd⟩

/-- **Present derivations have witnessed heads.** Under a closed
    contribution assignment, the head of every derivation present
    in the folded hypergraph is a witnessed node of it. -/
theorem head_witnessed {Node Ev : Type} (lift : Ev → Graph Node)
    (closed : Closed lift) {l : List Ev} {d : Derivation Node}
    (present : (fold lift l).edges d = true) :
    (fold lift l).nodes d.head = true := by
  rcases (fold_edges lift).mp present with ⟨e, he, hd⟩
  exact (fold_nodes lift).mpr ⟨e, he, closed e d hd⟩

/-- **Witnessed heads, both directions.** Under a headed and
    closed contribution assignment, a node is witnessed in the
    folded hypergraph exactly when it is the head of a derivation
    present in it. -/
theorem returns_headed_iff {Node Ev : Type} (lift : Ev → Graph Node)
    (headed : Headed lift) (closed : Closed lift)
    {l : List Ev} {n : Node} :
    (fold lift l).nodes n = true ↔
      ∃ d, (fold lift l).edges d = true ∧ d.head = n := by
  constructor
  · intro h
    rcases returns_headed lift headed h with ⟨d, hd, hh, _⟩
    exact ⟨d, hd, hh⟩
  · intro h
    rcases h with ⟨d, hd, hh⟩
    rw [← hh]
    exact head_witnessed lift closed hd

/-- **Returned premises are witnessed.** Under a grounded
    contribution assignment, every premise of every derivation
    present in the folded hypergraph is a witnessed node of it,
    so the premise set read off a returned derivation names only
    witnessed nodes. -/
theorem returned_premises_witnessed {Node Ev : Type}
    (lift : Ev → Graph Node) (grounded : Grounded lift)
    {l : List Ev} {d : Derivation Node} {m : Node}
    (present : (fold lift l).edges d = true)
    (premise : d.premises m = true) :
    (fold lift l).nodes m = true := by
  rcases (fold_edges lift).mp present with ⟨e, he, hd⟩
  exact (fold_nodes lift).mpr ⟨e, he, grounded e d m hd premise⟩

/-- **Headedness is the return at one event.** A contribution
    assignment is headed exactly when the return of a witnessed
    head holds on every one-event stream. So `returns_headed` says
    that the return at one event carries over to every stream:
    a closure of the property under the fold, not a fresh
    property. -/
theorem headed_iff_singleton {Node Ev : Type} (lift : Ev → Graph Node) :
    Headed lift ↔
      ∀ e n, (fold lift [e]).nodes n = true →
        ∃ d, (fold lift [e]).edges d = true ∧ d.head = n := by
  constructor
  · intro h e n hn
    have hs : fold lift [e] = lift e := join_empty_right (lift e)
    rw [hs] at hn ⊢
    exact h e n hn
  · intro h e n hn
    have hs : fold lift [e] = lift e := join_empty_right (lift e)
    have h1 := h e n (by rw [hs]; exact hn)
    rw [hs] at h1
    exact h1

/-- **Uniqueness of a returned premise set is a stream premise.**
    The folded hypergraph holds at most one present derivation per
    head exactly when the contributions of the whole stream hold at
    most one derivation per head. Any hypothesis that makes the
    returned premise set unique is therefore this conclusion
    restated across the stream, and is not offered as a result. -/
theorem unique_iff_contributed_unique {Node Ev : Type}
    (lift : Ev → Graph Node) {l : List Ev} :
    (∀ d d' : Derivation Node, (fold lift l).edges d = true →
      (fold lift l).edges d' = true → d.head = d'.head → d = d') ↔
    (∀ e e' (d d' : Derivation Node), e ∈ l → e' ∈ l →
      (lift e).edges d = true → (lift e').edges d' = true →
        d.head = d'.head → d = d') := by
  constructor
  · intro h e e' d d' he he' hd hd' hh
    exact h d d' ((fold_edges lift).mpr ⟨e, he, hd⟩)
      ((fold_edges lift).mpr ⟨e', he', hd'⟩) hh
  · intro h d d' hd hd' hh
    rcases (fold_edges lift).mp hd with ⟨e, he, hce⟩
    rcases (fold_edges lift).mp hd' with ⟨e', he', hce'⟩
    exact h e e' d d' he he' hce hce' hh

/-- The concrete recorder of Traceability is headed: the return
    proven there for it is an instance of `returns_headed`. -/
theorem recordLift_headed {Node Ev : Type} [DecidableEq Node]
    [DecidableEq (Derivation Node)] (record : Ev → Derivation Node) :
    Headed (recordLift record) := by
  intro e n hn
  exact ⟨record e, by simp [recordLift], by simpa [recordLift] using hn⟩

/-- The concrete recorder of Traceability is closed. -/
theorem recordLift_closed {Node Ev : Type} [DecidableEq Node]
    [DecidableEq (Derivation Node)] (record : Ev → Derivation Node) :
    Closed (recordLift record) := by
  intro e d hd
  have h : record e = d := by simpa [recordLift] using hd
  subst h
  simp [recordLift]

end HeadedReturn
