/-
  Adversarial controls for the witness hypergraph fold.

  Each control weakens the construction of Traceability along one
  axis, states the claim the weakening attacks, and proves that
  the claim fails for the weakened variant, on concrete data
  checked by the kernel. The controls are regression fixtures:
  if a future change reintroduces one of these weakenings into
  the main construction, the corresponding control is the shape
  of the failure to look for, and the main theorems are the proof
  that the unweakened construction does not have it.
-/

import Traceability

namespace Controls

open Traceability

/-- The counting accounting: how many times each node was
    contributed, as a natural number per node. Its join adds
    counts instead of taking the union, so it drops the
    idempotence the characteristic-function join has. -/
def countjoin (a b : Nat → Nat) : Nat → Nat :=
  fun n => a n + b n

/-- The contribution of one event to the counting accounting. -/
def countsingle (e : Nat) : Nat → Nat :=
  fun n => if n = e then 1 else 0

/-- The counting fold: the fold of a stream under the counting
    join. This is the weakened variant of the main fold. -/
def countfold : List Nat → (Nat → Nat)
  | [] => fun _ => 0
  | e :: es => countjoin (countsingle e) (countfold es)

/-- On the concrete stream, the counting fold counts the single
    presentation once. Checked by the kernel. -/
theorem count_once : countfold [0] 0 = 1 := by decide

/-- On the concrete stream, the counting fold counts the doubled
    presentation twice. Checked by the kernel. -/
theorem count_twice : countfold ([0] ++ [0]) 0 = 2 := by decide

/-- Control for duplication independence, against the counting
    variant: the weakened claim that presenting every event
    twice changes nothing is false for the counting fold. -/
theorem count_claim_fails :
    ¬ (∀ l : List Nat, countfold (l ++ l) = countfold l) := by
  intro h
  have h0 := congrFun (h [0]) 0
  rw [count_twice, count_once] at h0
  exact (by decide : (2 : Nat) ≠ 1) h0

/-- The first fold: a fold that reads only the first event of
    the stream and drops the rest. It reads arrival order, where
    the main fold reads only membership. -/
def firstfold (lift : Nat → Graph Nat) : List Nat → Graph Nat
  | [] => empty
  | e :: _ => lift e

/-- A concrete contribution assignment for the order control:
    each event contributes exactly its own node. -/
def ownlift (e : Nat) : Graph Nat :=
  ⟨fun n => decide (n = e), fun _ => false⟩

/-- The two concrete streams of the order control present the
    same set of events. -/
theorem swap_same_set : ∀ x : Nat, x ∈ [0, 1] ↔ x ∈ [1, 0] :=
  fun x => (List.Perm.swap 1 0 []).mem_iff (a := x)

/-- Control for order independence, against the first fold: the
    weakened claim that two streams with the same membership
    fold equally is false for the first fold. -/
theorem first_claim_fails :
    ¬ (∀ l₁ l₂ : List Nat,
      (∀ x, x ∈ l₁ ↔ x ∈ l₂) → firstfold ownlift l₁ = firstfold ownlift l₂) := by
  intro h
  have heq := h [0, 1] [1, 0] swap_same_set
  have h0 := congrFun (congrArg Graph.nodes heq) 0
  simp [firstfold, ownlift] at h0

/-- The first concrete derivation of the grain control: head one,
    every premise present. -/
def fullprem : Derivation Nat :=
  ⟨fun _ => true, 1⟩

/-- The second concrete derivation of the grain control: head
    one, no premise present. It shares the head of the first and
    differs in its premise set. -/
def noprem : Derivation Nat :=
  ⟨fun _ => false, 1⟩

/-- The two derivations of the grain control are different,
    because their premise sets differ at node zero. -/
theorem prem_differ : fullprem ≠ noprem := by
  intro h
  have h1 := congrArg Derivation.premises h
  have h2 := congrFun h1 0
  simp [fullprem, noprem] at h2

/-- A concrete contribution assignment for the grain control:
    every event contributes exactly the derivations whose first
    premise is present and whose head is one. It contributes the
    first derivation and not the second. -/
def grainlift (_e : Nat) : Graph Nat :=
  ⟨fun _ => false, fun d => d.premises 0 && decide (d.head = 1)⟩

/-- At the exact grain, the second derivation is absent from the
    folded hypergraph of the concrete stream. -/
theorem grain_absent : (fold grainlift [0]).edges noprem = false := by
  cases h : (fold grainlift [0]).edges noprem with
  | false => rfl
  | true =>
    rcases (fold_edges grainlift).mp h with ⟨e, he, hce⟩
    simp at he
    subst he
    simp [grainlift, noprem] at hce

/-- At the coarse grain, where a derivation is read as present
    when some present derivation shares its head, the second
    derivation reads as present: the first derivation is present
    and shares its head. -/
theorem grain_coarse_present :
    ∃ d', (fold grainlift [0]).edges d' = true ∧ d'.head = noprem.head := by
  refine ⟨fullprem, ?_, rfl⟩
  rw [fold_edges grainlift]
  exact ⟨0, by simp, by simp [grainlift, fullprem]⟩

/-- Control for provable returns, against the coarse grain: the
    weakened claim that head-grain presence gives exact presence
    is false. The premise set read off at the coarse grain is
    wrong for the second derivation: it reads as present while
    its exact record is absent. -/
theorem grain_claim_fails :
    ¬ (∀ d : Derivation Nat,
      (∃ d', (fold grainlift [0]).edges d' = true ∧ d'.head = d.head) →
        (fold grainlift [0]).edges d = true) := by
  intro h
  have hpres := h noprem grain_coarse_present
  rw [grain_absent] at hpres
  exact Bool.false_ne_true hpres

/-- A concrete contribution assignment for the return control:
    every event contributes node one and no derivation at all.
    Under this assignment the head of the second grain derivation
    is witnessed by every stream, and nothing is ever
    contributed. -/
def beacon (_e : Nat) : Graph Nat :=
  ⟨fun n => decide (n = 1), fun _ => false⟩

/-- Under the return control's assignment, the head of the
    second grain derivation is a witnessed node of the folded
    hypergraph of the concrete stream. -/
theorem marked : (fold beacon [0]).nodes noprem.head = true :=
  (fold_nodes beacon).mpr ⟨0, by simp, by simp [beacon, noprem]⟩

/-- Under the return control's assignment, the second grain
    derivation is absent from the folded hypergraph of the
    concrete stream: no event contributes it. -/
theorem absent : (fold beacon [0]).edges noprem = false := by
  cases h : (fold beacon [0]).edges noprem with
  | false => rfl
  | true =>
    rcases (fold_edges beacon).mp h with ⟨e, he, hce⟩
    simp at he
    subst he
    simp [beacon] at hce

/-- Control for provable returns, against the witnessed head:
    the claim that a derivation whose head is a witnessed node
    of the fold is present in the fold is false. The concrete
    stream witnesses the head and contributes nothing, and the
    derivation stays absent. Head witnessing alone returns
    nothing; contribution is the load-bearing hypothesis of
    `returns_head`. -/
theorem separation :
    ¬ (∀ (lift : Nat → Graph Nat) (l : List Nat) (d : Derivation Nat),
      (fold lift l).nodes d.head = true →
        (fold lift l).edges d = true) := by
  intro h
  have hpres := h beacon [0] noprem marked
  rw [absent] at hpres
  exact Bool.false_ne_true hpres

/-- A contribution returns with no witnessed head: under the
    grain assignment, which contributes derivations and no
    nodes at all, the first grain derivation is present in the
    fold while its head is not a witnessed node. The
    witnessed-head hypothesis of the earlier form of
    `returns_head` was therefore not necessary either. -/
theorem unwitnessed :
    (fold grainlift [0]).edges fullprem = true ∧
      (fold grainlift [0]).nodes fullprem.head = false := by
  constructor
  · exact (fold_edges grainlift).mpr
      ⟨0, by simp, by simp [grainlift, fullprem]⟩
  · cases h : (fold grainlift [0]).nodes fullprem.head with
    | false => rfl
    | true =>
      rcases (fold_nodes grainlift).mp h with ⟨e, he, hce⟩
      simp at he
      subst he
      simp [grainlift] at hce

/-- The residue fold: a retraction variant whose derivation face
    is retracted exactly, but whose node face keeps the nodes of
    the full, unretracted fold joined in. Retracted events leave
    residue on the node face. -/
def residuefold (lift : Nat → Graph Nat) (keep : Nat → Bool)
    (l : List Nat) : Graph Nat :=
  ⟨fun n => (fold lift (l.filter keep)).nodes n || (fold lift l).nodes n,
    (fold lift (l.filter keep)).edges⟩

/-- The surviving fold of the residue control has node zero
    absent: only event one survives, and it contributes node
    one, not node zero. -/
theorem residue_survivor_absent :
    (fold ownlift ([0, 1].filter (fun e => decide (e = 1)))).nodes 0 = false := by
  cases h : (fold ownlift ([0, 1].filter (fun e => decide (e = 1)))).nodes 0 with
  | false => rfl
  | true =>
    rcases (fold_nodes ownlift).mp h with ⟨e, he, hce⟩
    simp at he
    subst he
    simp [ownlift] at hce

/-- The residue fold of the residue control has node zero
    present: the retracted event zero leaves its node behind. -/
theorem residue_present :
    (residuefold ownlift (fun e => decide (e = 1)) [0, 1]).nodes 0 = true := by
  show ((fold ownlift ([0, 1].filter (fun e => decide (e = 1)))).nodes 0 ||
    (fold ownlift [0, 1]).nodes 0) = true
  rw [Bool.or_eq_true]
  exact Or.inr ((fold_nodes ownlift).mpr ⟨0, by simp, by simp [ownlift]⟩)

/-- Control for retraction exactness, against the residue fold:
    the weakened claim that the retracted fold equals the fold
    of the survivors is false for the residue fold. -/
theorem residue_claim_fails :
    residuefold ownlift (fun e => decide (e = 1)) [0, 1] ≠
      fold ownlift ([0, 1].filter (fun e => decide (e = 1))) := by
  intro h
  have h0 := congrFun (congrArg Graph.nodes h) 0
  rw [residue_present, residue_survivor_absent] at h0
  exact Bool.noConfusion h0

#print axioms count_once
#print axioms count_twice
#print axioms count_claim_fails
#print axioms swap_same_set
#print axioms first_claim_fails
#print axioms prem_differ
#print axioms grain_absent
#print axioms grain_coarse_present
#print axioms grain_claim_fails
#print axioms marked
#print axioms absent
#print axioms separation
#print axioms unwitnessed
#print axioms residue_survivor_absent
#print axioms residue_present
#print axioms residue_claim_fails

#check @Controls.countjoin
#check @Controls.countsingle
#check @Controls.countfold
#check @Controls.count_once
#check @Controls.count_twice
#check @Controls.count_claim_fails
#check @Controls.firstfold
#check @Controls.ownlift
#check @Controls.swap_same_set
#check @Controls.first_claim_fails
#check @Controls.fullprem
#check @Controls.noprem
#check @Controls.prem_differ
#check @Controls.grainlift
#check @Controls.grain_absent
#check @Controls.grain_coarse_present
#check @Controls.grain_claim_fails
#check @Controls.beacon
#check @Controls.marked
#check @Controls.absent
#check @Controls.separation
#check @Controls.unwitnessed
#check @Controls.residuefold
#check @Controls.residue_survivor_absent
#check @Controls.residue_present
#check @Controls.residue_claim_fails

end Controls
