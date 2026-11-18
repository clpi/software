/-
  Platform independence of the historical witness hypergraph.

  Every execution appends witnesses to an append-only ledger. The
  historical witness hypergraph is the fold of the witness stream:
  nodes for symbols and witnessed elements, hyperedges carrying a
  full premise set to a conclusion. Witnesses carry exact time,
  but the hypergraph is a function of the witness set alone.

  The fold is quantified over arbitrary types for nodes, events
  and times, and over an arbitrary contribution assignment that
  assigns to each event the nodes and derivations it contributes.
  That arbitrariness is the independence: the theorems hold for
  every such assignment, so no hypothesis names a particular
  environment, mechanism or program. This file states the
  independence in its own comments only; the proof terms below
  contain no such name.
-/

namespace Traceability

/-- A derivation: a premise characteristic function over nodes
    together with a head node. The premise set is the whole
    function, so a hyperedge carries its full premise set. -/
structure Derivation (Node : Type) where
  premises : Node → Bool
  head : Node

/-- A hypergraph: a pair of characteristic functions, which nodes
    are present and which derivations are present. -/
structure Graph (Node : Type) where
  nodes : Node → Bool
  edges : Derivation Node → Bool

/-- The pointwise join of two hypergraphs: union on both faces. -/
def join {Node : Type} (g h : Graph Node) : Graph Node :=
  ⟨fun n => g.nodes n || h.nodes n, fun d => g.edges d || h.edges d⟩

/-- The empty hypergraph: nothing present. -/
def empty {Node : Type} : Graph Node :=
  ⟨fun _ => false, fun _ => false⟩

/-- The fold of an event stream: the pointwise join over the
    stream's events of their contributions, under an arbitrary
    contribution assignment. -/
def fold {Node Ev : Type} (lift : Ev → Graph Node) : List Ev → Graph Node
  | [] => empty
  | e :: es => join (lift e) (fold lift es)

/-- A timed event: an underlying event together with its exact
    time, taken from an arbitrary time type. -/
structure Timed (Ev Time : Type) where
  event : Ev
  time : Time

/-- The fold of a timed stream. It is defined through the
    underlying events' contributions only; the time components
    are carried by the stream and never read by the fold. -/
def foldtimed {Node Ev Time : Type} (lift : Ev → Graph Node)
    (l : List (Timed Ev Time)) : Graph Node :=
  fold lift (l.map Timed.event)

/-- Two booleans that agree on being true are equal. -/
theorem bool_eq_of_agree {a b : Bool} (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp_all

/-- Hypergraphs that agree pointwise on both faces are equal. -/
theorem graph_ext {Node : Type} {g h : Graph Node}
    (hn : ∀ n, g.nodes n = h.nodes n)
    (he : ∀ d, g.edges d = h.edges d) : g = h := by
  cases g with
  | mk gn ge =>
    cases h with
    | mk hn' he' =>
      have h1 : gn = hn' := funext hn
      have h2 : ge = he' := funext he
      rw [h1, h2]

/-- The join is associative. -/
theorem join_assoc {Node : Type} (a b c : Graph Node) :
    join (join a b) c = join a (join b c) := by
  apply graph_ext
  · intro n
    show ((a.nodes n || b.nodes n) || c.nodes n) =
      (a.nodes n || (b.nodes n || c.nodes n))
    cases a.nodes n <;> cases b.nodes n <;> cases c.nodes n <;> rfl
  · intro d
    show ((a.edges d || b.edges d) || c.edges d) =
      (a.edges d || (b.edges d || c.edges d))
    cases a.edges d <;> cases b.edges d <;> cases c.edges d <;> rfl

/-- The join is commutative. -/
theorem join_comm {Node : Type} (a b : Graph Node) :
    join a b = join b a := by
  apply graph_ext
  · intro n
    show (a.nodes n || b.nodes n) = (b.nodes n || a.nodes n)
    cases a.nodes n <;> cases b.nodes n <;> rfl
  · intro d
    show (a.edges d || b.edges d) = (b.edges d || a.edges d)
    cases a.edges d <;> cases b.edges d <;> rfl

/-- The join is idempotent. -/
theorem join_idem {Node : Type} (a : Graph Node) : join a a = a := by
  apply graph_ext
  · intro n
    show (a.nodes n || a.nodes n) = a.nodes n
    cases a.nodes n <;> rfl
  · intro d
    show (a.edges d || a.edges d) = a.edges d
    cases a.edges d <;> rfl

/-- The empty hypergraph is a left identity for the join. -/
theorem join_empty_left {Node : Type} (a : Graph Node) :
    join empty a = a := by
  apply graph_ext
  · intro n
    show (false || a.nodes n) = a.nodes n
    cases a.nodes n <;> rfl
  · intro d
    show (false || a.edges d) = a.edges d
    cases a.edges d <;> rfl

/-- The empty hypergraph is a right identity for the join. -/
theorem join_empty_right {Node : Type} (a : Graph Node) :
    join a empty = a := by
  apply graph_ext
  · intro n
    show (a.nodes n || false) = a.nodes n
    cases a.nodes n <;> rfl
  · intro d
    show (a.edges d || false) = a.edges d
    cases a.edges d <;> rfl

/-- The fold splits over appends: a recompute over a partitioned
    stream agrees with the join of the parts. -/
theorem fold_append {Node Ev : Type} (lift : Ev → Graph Node)
    (l₁ l₂ : List Ev) :
    fold lift (l₁ ++ l₂) = join (fold lift l₁) (fold lift l₂) := by
  induction l₁ with
  | nil => simp [fold, join_empty_left]
  | cons e es ih =>
    show join (lift e) (fold lift (es ++ l₂)) =
      join (join (lift e) (fold lift es)) (fold lift l₂)
    rw [ih, join_assoc]

/-- What the fold records on the node face is exactly what some
    event of the stream contributes: nothing added, nothing lost. -/
theorem fold_nodes {Node Ev : Type} (lift : Ev → Graph Node)
    {l : List Ev} {n : Node} :
    (fold lift l).nodes n = true ↔
      ∃ e, e ∈ l ∧ (lift e).nodes n = true := by
  induction l with
  | nil =>
    constructor
    · intro h
      simp [fold, empty] at h
    · intro h
      rcases h with ⟨e, he, _⟩
      simp at he
  | cons e es ih =>
    constructor
    · intro h
      have h' : ((lift e).nodes n || (fold lift es).nodes n) = true := h
      rw [Bool.or_eq_true] at h'
      rcases h' with h1 | h1
      · exact ⟨e, List.mem_cons_self, h1⟩
      · rcases ih.mp h1 with ⟨e', he', hce'⟩
        exact ⟨e', List.mem_cons_of_mem e he', hce'⟩
    · intro h
      rcases h with ⟨e', he', hce'⟩
      show ((lift e).nodes n || (fold lift es).nodes n) = true
      rw [Bool.or_eq_true]
      cases he' with
      | head _ => exact Or.inl hce'
      | tail _ hmem => exact Or.inr (ih.mpr ⟨e', hmem, hce'⟩)

/-- What the fold records on the derivation face is exactly what
    some event of the stream contributes: a derivation is present
    in the folded hypergraph if and only if at least one event in
    the stream contributes it, so the premise set of every
    witnessed conclusion is read off the hypergraph exactly as
    recorded, nothing added and nothing lost. -/
theorem fold_edges {Node Ev : Type} (lift : Ev → Graph Node)
    {l : List Ev} {d : Derivation Node} :
    (fold lift l).edges d = true ↔
      ∃ e, e ∈ l ∧ (lift e).edges d = true := by
  induction l with
  | nil =>
    constructor
    · intro h
      simp [fold, empty] at h
    · intro h
      rcases h with ⟨e, he, _⟩
      simp at he
  | cons e es ih =>
    constructor
    · intro h
      have h' : ((lift e).edges d || (fold lift es).edges d) = true := h
      rw [Bool.or_eq_true] at h'
      rcases h' with h1 | h1
      · exact ⟨e, List.mem_cons_self, h1⟩
      · rcases ih.mp h1 with ⟨e', he', hce'⟩
        exact ⟨e', List.mem_cons_of_mem e he', hce'⟩
    · intro h
      rcases h with ⟨e', he', hce'⟩
      show ((lift e).edges d || (fold lift es).edges d) = true
      rw [Bool.or_eq_true]
      cases he' with
      | head _ => exact Or.inl hce'
      | tail _ hmem => exact Or.inr (ih.mpr ⟨e', hmem, hce'⟩)

/-- Every derivation that any event contributes and whose head is
    a witnessed node of the folded hypergraph is present in the
    folded hypergraph. -/
theorem returns_head {Node Ev : Type} (lift : Ev → Graph Node)
    {l : List Ev} {d : Derivation Node}
    (_witnessed : (fold lift l).nodes d.head = true)
    (contributed : ∃ e, e ∈ l ∧ (lift e).edges d = true) :
    (fold lift l).edges d = true :=
  (fold_edges lift).mpr contributed

/-- **Order and duplication independence.** Two streams with the
    same membership have equal folds. The fold is a function of
    the set of events, not of the stream that presented it. -/
theorem fold_ext {Node Ev : Type} (lift : Ev → Graph Node)
    {l₁ l₂ : List Ev} (h : ∀ e, e ∈ l₁ ↔ e ∈ l₂) :
    fold lift l₁ = fold lift l₂ := by
  apply graph_ext
  · intro n
    apply bool_eq_of_agree
    rw [fold_nodes lift, fold_nodes lift]
    constructor
    · intro hc
      rcases hc with ⟨e, he, hce⟩
      exact ⟨e, (h e).mp he, hce⟩
    · intro hc
      rcases hc with ⟨e, he, hce⟩
      exact ⟨e, (h e).mpr he, hce⟩
  · intro d
    apply bool_eq_of_agree
    rw [fold_edges lift, fold_edges lift]
    constructor
    · intro hc
      rcases hc with ⟨e, he, hce⟩
      exact ⟨e, (h e).mp he, hce⟩
    · intro hc
      rcases hc with ⟨e, he, hce⟩
      exact ⟨e, (h e).mpr he, hce⟩

/-- **Permutation independence**: reordering the stream changes
    nothing. -/
theorem fold_perm {Node Ev : Type} (lift : Ev → Graph Node)
    {l₁ l₂ : List Ev} (h : List.Perm l₁ l₂) :
    fold lift l₁ = fold lift l₂ :=
  fold_ext lift (fun e => h.mem_iff (a := e))

/-- **Duplication independence**: presenting every event twice
    changes nothing. -/
theorem fold_append_self {Node Ev : Type} (lift : Ev → Graph Node)
    (l : List Ev) : fold lift (l ++ l) = fold lift l := by
  rw [fold_append]
  apply graph_ext
  · intro n
    show ((fold lift l).nodes n || (fold lift l).nodes n) =
      (fold lift l).nodes n
    cases (fold lift l).nodes n <;> rfl
  · intro d
    show ((fold lift l).edges d || (fold lift l).edges d) =
      (fold lift l).edges d
    cases (fold lift l).edges d <;> rfl

/-- **Time independence, membership form.** Two timed streams
    whose underlying events have the same membership have equal
    folds, whatever their time components are. -/
theorem foldtimed_ext {Node Ev Time : Type} (lift : Ev → Graph Node)
    {l₁ l₂ : List (Timed Ev Time)}
    (h : ∀ e, e ∈ l₁.map Timed.event ↔ e ∈ l₂.map Timed.event) :
    foldtimed lift l₁ = foldtimed lift l₂ :=
  fold_ext lift h

/-- Mapping a stream to timed events and projecting back to the
    underlying events returns the stream, for any time assignment. -/
theorem map_event {Ev Time : Type} (es : List Ev) (t : Ev → Time) :
    (es.map fun e => Timed.mk e (t e)).map Timed.event = es := by
  induction es with
  | nil => rfl
  | cons a as ih => simp [ih]

/-- **Time independence, reassignment form.** Reassigning every
    time component of a stream, keeping the underlying events in
    place, leaves the folded hypergraph unchanged. -/
theorem foldtimed_retime {Node Ev Time : Type} (lift : Ev → Graph Node)
    (es : List Ev) (f g : Ev → Time) :
    foldtimed lift (es.map fun e => Timed.mk e (f e)) =
      foldtimed lift (es.map fun e => Timed.mk e (g e)) := by
  unfold foldtimed
  rw [map_event es f, map_event es g]

/-- **Retraction exactness, node face.** After retracting to the
    events that survive a test, a node is present in the filtered
    fold if and only if some surviving event of the original
    stream contributes it. -/
theorem retract_nodes {Node Ev : Type} (lift : Ev → Graph Node)
    (keep : Ev → Bool) {l : List Ev} {n : Node} :
    (fold lift (l.filter keep)).nodes n = true ↔
      ∃ e, e ∈ l ∧ keep e = true ∧ (lift e).nodes n = true := by
  rw [fold_nodes lift]
  constructor
  · intro h
    rcases h with ⟨e, he, hce⟩
    rw [List.mem_filter] at he
    exact ⟨e, he.1, he.2, hce⟩
  · intro h
    rcases h with ⟨e, he, hke, hce⟩
    exact ⟨e, List.mem_filter.mpr ⟨he, hke⟩, hce⟩

/-- **Retraction exactness, derivation face.** After retracting
    to the events that survive a test, a derivation is present in
    the filtered fold if and only if some surviving event of the
    original stream contributes it. -/
theorem retract_edges {Node Ev : Type} (lift : Ev → Graph Node)
    (keep : Ev → Bool) {l : List Ev} {d : Derivation Node} :
    (fold lift (l.filter keep)).edges d = true ↔
      ∃ e, e ∈ l ∧ keep e = true ∧ (lift e).edges d = true := by
  rw [fold_edges lift]
  constructor
  · intro h
    rcases h with ⟨e, he, hce⟩
    rw [List.mem_filter] at he
    exact ⟨e, he.1, he.2, hce⟩
  · intro h
    rcases h with ⟨e, he, hke, hce⟩
    exact ⟨e, List.mem_filter.mpr ⟨he, hke⟩, hce⟩

/-- **Retraction exactness, recomputation form.** Folding the
    filtered stream yields exactly the hypergraph of the
    surviving event set: any stream presenting exactly the
    survivors folds to the same hypergraph. Observables after
    retraction equal recomputation from the survivors. -/
theorem retract_eq {Node Ev : Type} (lift : Ev → Graph Node)
    (keep : Ev → Bool) {l s : List Ev}
    (h : ∀ e, e ∈ s ↔ e ∈ l ∧ keep e = true) :
    fold lift (l.filter keep) = fold lift s := by
  apply fold_ext lift
  intro e
  rw [List.mem_filter]
  exact (h e).symm

#print axioms fold_nodes
#print axioms fold_edges
#print axioms returns_head
#print axioms fold_ext
#print axioms fold_perm
#print axioms fold_append_self
#print axioms foldtimed_ext
#print axioms foldtimed_retime
#print axioms retract_nodes
#print axioms retract_edges
#print axioms retract_eq
#print axioms fold_append
#print axioms join_assoc
#print axioms join_comm
#print axioms join_idem

/- Statement enumeration for the mechanical platform audit: the
   type of every definition and theorem above, printed by the
   kernel checker and scanned by the audit script. -/
#check @Traceability.Derivation
#check @Traceability.Graph
#check @Traceability.join
#check @Traceability.empty
#check @Traceability.fold
#check @Traceability.Timed
#check @Traceability.foldtimed
#check @Traceability.bool_eq_of_agree
#check @Traceability.graph_ext
#check @Traceability.join_assoc
#check @Traceability.join_comm
#check @Traceability.join_idem
#check @Traceability.join_empty_left
#check @Traceability.join_empty_right
#check @Traceability.fold_append
#check @Traceability.fold_nodes
#check @Traceability.fold_edges
#check @Traceability.returns_head
#check @Traceability.fold_ext
#check @Traceability.fold_perm
#check @Traceability.fold_append_self
#check @Traceability.foldtimed_ext
#check @Traceability.map_event
#check @Traceability.foldtimed_retime
#check @Traceability.retract_nodes
#check @Traceability.retract_edges
#check @Traceability.retract_eq

end Traceability
