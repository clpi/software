/- Preservation: the derivation-carrying compiler admits recovery of the
   qualified quotient from the artifact; premise cones read off the
   artifact are exact; joins commute at the level of the topology. -/
import Basic

namespace CompilersLoseInfo

variable {A : Type}

/-- Recovery is a retraction on the quotient: the quotient of a program is
    read back off its carried artifact, exactly. -/
theorem carry_recovers (g : Hypergraph A) : recover (carry g) = qual g := rfl

/-- So the carrying compiler admits recovery, where the forgetting
    compiler provably does not. -/
theorem carry_recoverable : Recoverable (carry (A := A)) (qual (A := A)) :=
  ⟨recover, carry_recovers⟩

/-- The premise cone as read from an artifact. -/
def coneOf (x : Artifact A) (b : A) : A → Prop := fun a => x.topology a b

/-- Cones from the artifact are the source's cones, exactly — the data a
    premise-cone-scoped revalidation or a test selection runs over needs
    no reconstruction. -/
theorem cone_exact (g : Hypergraph A) (b : A) :
    coneOf (carry g) b = cone g b := rfl

/-- Derivation grows under merge, from either side. (One direction only,
    and stated so: a merge can derive more than either part, through
    hyperedges that mix the two. The behavior of a merge is the closure of
    the merged graph, never a combination of the parts' behaviors.) -/
theorem derives_merge_left {g₁ g₂ : Hypergraph A} {a : A}
    (h : Derives g₁ a) : Derives (merge g₁ g₂) a := by
  induction h with
  | root hr => exact Derives.root (Or.inl hr)
  | step he _ ih => exact Derives.step (Or.inl he) ih

theorem derives_merge_right {g₁ g₂ : Hypergraph A} {a : A}
    (h : Derives g₂ a) : Derives (merge g₁ g₂) a := by
  induction h with
  | root hr => exact Derives.root (Or.inr hr)
  | step he _ ih => exact Derives.step (Or.inr he) ih

/-- Reachability is monotone under merge, from either side. -/
theorem reaches_merge_left {g₁ g₂ : Hypergraph A} {a b : A}
    (h : Reaches g₁ a b) : Reaches (merge g₁ g₂) a b := by
  induction h with
  | refl => exact Reaches.refl
  | step he => obtain ⟨ps, hf, hm⟩ := he; exact Reaches.step ⟨ps, Or.inl hf, hm⟩
  | trans _ _ ih₁ ih₂ => exact Reaches.trans ih₁ ih₂

theorem reaches_merge_right {g₁ g₂ : Hypergraph A} {a b : A}
    (h : Reaches g₂ a b) : Reaches (merge g₁ g₂) a b := by
  induction h with
  | refl => exact Reaches.refl
  | step he => obtain ⟨ps, hf, hm⟩ := he; exact Reaches.step ⟨ps, Or.inr hf, hm⟩
  | trans _ _ ih₁ ih₂ => exact Reaches.trans ih₁ ih₂

/-- The edges of a merge are the union of the edges, by definition. -/
theorem merge_edges {g₁ g₂ : Hypergraph A} {ps : List A} {b : A} :
    (merge g₁ g₂).edges ps b ↔ g₁.edges ps b ∨ g₂.edges ps b := Iff.rfl

/-- The join of two relations: either relation, closed under transitivity.
    This is the transitive closure of the union — the topology a merged
    program must have if compiling the parts and joining is to agree with
    merging and compiling. -/
inductive RelJoin (R S : A → A → Prop) : A → A → Prop where
  | left {a b} : R a b → RelJoin R S a b
  | right {a b} : S a b → RelJoin R S a b
  | trans {a b c} : RelJoin R S a b → RelJoin R S b c → RelJoin R S a c

/-- The topology of a merge is exactly the join of the topologies: a chain
    in the merged graph alternates between the two graphs' hyperedges, and
    every such alternation is a join chain. -/
theorem reaches_merge {g₁ g₂ : Hypergraph A} {a b : A} :
    Reaches (merge g₁ g₂) a b ↔ RelJoin (Reaches g₁) (Reaches g₂) a b := by
  constructor
  · intro h
    induction h with
    | refl => exact RelJoin.left Reaches.refl
    | step he =>
      obtain ⟨ps, hf, hm⟩ := he
      have hf' := merge_edges.mp hf
      cases hf' with
      | inl h₁ => exact RelJoin.left (Reaches.step ⟨ps, h₁, hm⟩)
      | inr h₂ => exact RelJoin.right (Reaches.step ⟨ps, h₂, hm⟩)
    | trans _ _ ih₁ ih₂ => exact RelJoin.trans ih₁ ih₂
  · intro h
    induction h with
    | left h₁ => exact reaches_merge_left h₁
    | right h₂ => exact reaches_merge_right h₂
    | trans _ _ ih₁ ih₂ => exact Reaches.trans ih₁ ih₂

/-- Joins commute with compilation at the level of the topology: merging
    first and compiling second yields the same topology as compiling first
    and joining second. -/
theorem topology_join_commutes (g₁ g₂ : Hypergraph A) :
    (carry (merge g₁ g₂)).topology
      = RelJoin (carry g₁).topology (carry g₂).topology := by
  funext a b
  apply propext
  exact reaches_merge

end CompilersLoseInfo
