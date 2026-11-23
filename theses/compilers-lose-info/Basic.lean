/- Basic objects for the topological thesis: programs as derivation
   hypergraphs in the family's form, derivation, reachability, the qualified
   quotient, compilers and recovery, and merge with its join laws. -/

namespace CompilersLoseInfo

/-- A program: a directed hypergraph over a type of nodes, in the form of
    HypergraphIncremental.Hypergraph in clpi/software-optimality — a root
    predicate and hyperedges from premise lists to conclusions. -/
structure Hypergraph (A : Type) where
  roots : A → Prop
  edges : List A → A → Prop

/-- Derivation: the least fixed point of the positive Horn rules — the same
    closure as Qualification.Derives in clpi/software-optimality, the closure
    clpi/software-is-quantifiable folds and colors over. -/
inductive Derives {A : Type} (g : Hypergraph A) : A → Prop where
  | root {a} : g.roots a → Derives g a
  | step {ps a} : g.edges ps a → (∀ p, p ∈ ps → Derives g p) → Derives g a

/-- Reachability: the dependency view of the hypergraph. One node reaches
    another when it occurs in a premise list on a chain of hyperedges
    concluding at the other. Firing a hyperedge still requires all of its
    premises; this relation is for scoping and provenance only. -/
inductive Reaches {A : Type} (g : Hypergraph A) : A → A → Prop where
  | refl {a} : Reaches g a a
  | step {a b} : (∃ ps, g.edges ps b ∧ a ∈ ps) → Reaches g a b
  | trans {a b c} : Reaches g a b → Reaches g b c → Reaches g a c

/-- The premise cone of a node: everything that reaches it. -/
def cone {A : Type} (g : Hypergraph A) (b : A) : A → Prop :=
  fun a => Reaches g a b

/-- The qualified quotient of a program: its behavior (which nodes derive)
    together with its topology (the reachability relation). Two programs
    agree on the qualified quotient when these pairs are equal — this is
    equivalence of terms under the derivation machinery, observed through
    everything the machinery derives about a program. -/
def qual {A : Type} (g : Hypergraph A) : (A → Prop) × (A → A → Prop) :=
  (fun a => Derives g a, fun a b => Reaches g a b)

/-- Agreement on the qualified quotient. -/
def Agree {A : Type} (g₁ g₂ : Hypergraph A) : Prop := qual g₁ = qual g₂

/-- The forgetting compiler: the artifact is the behavior alone. The
    topology is discarded — this is the conventional compiler, modeled at
    exactly the quotient the thesis measures loss against. -/
def forget {A : Type} (g : Hypergraph A) : A → Prop := fun a => Derives g a

/-- A carried artifact: behavior and topology as its own components. -/
structure Artifact (A : Type) where
  behavior : A → Prop
  topology : A → A → Prop

/-- The derivation-carrying compiler: compilation as a projection inside
    the one graph. The artifact carries the derivation structure. -/
def carry {A : Type} (g : Hypergraph A) : Artifact A where
  behavior := fun a => Derives g a
  topology := fun a b => Reaches g a b

/-- Reading the qualified quotient back off an artifact. -/
def recover {A : Type} (x : Artifact A) : (A → Prop) × (A → A → Prop) :=
  (x.behavior, x.topology)

/-- A compiler admits recovery of a quotient map when some function of the
    artifact returns every source's own quotient. -/
def Recoverable {S T Q : Type} (c : S → T) (q : S → Q) : Prop :=
  ∃ r : T → Q, ∀ s, r (c s) = q s

/-- Merge of programs: pointwise union of roots and hyperedges. -/
def merge {A : Type} (g₁ g₂ : Hypergraph A) : Hypergraph A where
  roots := fun a => g₁.roots a ∨ g₂.roots a
  edges := fun ps a => g₁.edges ps a ∨ g₂.edges ps a

/-- The information order on programs: pointwise inclusion of roots and
    hyperedges. -/
def Le {A : Type} (g₁ g₂ : Hypergraph A) : Prop :=
  (∀ a, g₁.roots a → g₂.roots a) ∧ (∀ ps a, g₁.edges ps a → g₂.edges ps a)

theorem le_refl {A : Type} (g : Hypergraph A) : Le g g :=
  ⟨fun _ h => h, fun _ _ h => h⟩

theorem le_trans {A : Type} {g₁ g₂ g₃ : Hypergraph A} :
    Le g₁ g₂ → Le g₂ g₃ → Le g₁ g₃ :=
  fun h₁ h₂ => ⟨fun a h => h₂.1 a (h₁.1 a h), fun ps a h => h₂.2 ps a (h₁.2 ps a h)⟩

theorem le_merge_left {A : Type} (g₁ g₂ : Hypergraph A) : Le g₁ (merge g₁ g₂) :=
  ⟨fun _ h => Or.inl h, fun _ _ h => Or.inl h⟩

theorem le_merge_right {A : Type} (g₁ g₂ : Hypergraph A) : Le g₂ (merge g₁ g₂) :=
  ⟨fun _ h => Or.inr h, fun _ _ h => Or.inr h⟩

theorem merge_least {A : Type} {g₁ g₂ g : Hypergraph A} :
    Le g₁ g → Le g₂ g → Le (merge g₁ g₂) g :=
  fun h₁ h₂ => ⟨fun a h => h.elim (h₁.1 a) (h₂.1 a),
    fun ps a h => h.elim (h₁.2 ps a) (h₂.2 ps a)⟩

/-- The foundation claim of the monotonicity program, in premise shape: a
    type of states carrying an information order and a merge that is the
    join. The instance over hypergraphs is proven in this repository
    (hypergraph_join below). The claim over the states of arbitrary
    software is an open spec point at its home in the monotonicity living
    spec; it is not proven here and no theorem in this repository uses it. -/
structure JoinSemilatticePremise (S : Type) where
  le : S → S → Prop
  join : S → S → S
  le_join_left : ∀ x y, le x (join x y)
  le_join_right : ∀ x y, le y (join x y)
  join_least : ∀ {x y z}, le x z → le y z → le (join x y) z

/-- The proven instance: hypergraphs under the information order, with
    merge as the join. -/
def hypergraph_join (A : Type) : JoinSemilatticePremise (Hypergraph A) where
  le := Le
  join := merge
  le_join_left := fun g₁ g₂ => le_merge_left g₁ g₂
  le_join_right := fun g₁ g₂ => le_merge_right g₁ g₂
  join_least := fun h₁ h₂ => merge_least h₁ h₂

end CompilersLoseInfo
