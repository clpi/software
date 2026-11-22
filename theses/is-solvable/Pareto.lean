import WitnessExecutable

/- The claim this repository carries that software-optimality does not:
   append accounting.  Each headline below is Pareto optimal within its
   variant lattice: its conclusion is an equivalence or an exact equation,
   and every premise it keeps is shown necessary by a kernel-checked
   counterexample in this file.  Points that were dominated (premises they
   did not need) are re-derived from their premise-free forms in
   WitnessExecutable.  Scope: premise subsets and conclusion forms of each
   stated theorem, not every possible theorem.

   Computability and exactness of the closure (`close_exact`) is imported
   from software-optimality and is not a result of this repository. -/
namespace Pareto
open Qualification Hyperlattice WitnessExecutable ExecutableClosure

section Headline
variable {A : Type} [DecidableEq A] {Axis : Type}

/-- Headline, premise-free: a coordinate strictly increases on append exactly
when some probe on that axis enters the executable closure. -/
theorem resolution_strict_iff_close (U : List A) (b w : Batch A)
    (probes : Axis → List A) (i : Axis) :
    resolution probes (classify U b) i < resolution probes (classify U (append b w)) i ↔
      ∃ x, x ∈ probes i ∧ x ∉ close U b.roots b.edges ∧
        x ∈ close U (append b w).roots (append b w).edges := by
  unfold resolution
  rw [count_strict_iff _ _ _ (fun x _ => classify_append_mono U b w x)]
  constructor
  · rintro ⟨x, hx, hp, hq⟩
    refine ⟨x, hx, fun h => ?_, (classify_iff U _ x).mp hq⟩
    rw [(classify_iff U b x).mpr h] at hp
    exact Bool.noConfusion hp
  · rintro ⟨x, hx, hn, hq⟩
    refine ⟨x, hx, ?_, (classify_iff U _ x).mpr hq⟩
    cases hp : classify U b x
    · rfl
    · exact absurd ((classify_iff U b x).mp hp) hn

/-- Headline, semantic form: with roots and rule heads in the universe, the
same characterization in terms of derivability in the authority graph. -/
theorem resolution_append_iff (U : List A) (b w : Batch A)
    (roots : ∀ a, a ∈ (append b w).roots → a ∈ U)
    (heads : ∀ ps a, (ps, a) ∈ (append b w).edges → a ∈ U)
    (probes : Axis → List A) (i : Axis) :
    resolution probes (classify U b) i < resolution probes (classify U (append b w)) i ↔
      ∃ x, x ∈ probes i ∧ ¬ Knowledge (authority b) x ∧
        Knowledge (authority (append b w)) x := by
  have rb : ∀ a, a ∈ b.roots → a ∈ U := fun a h => roots a (List.mem_append_left _ h)
  have hb : ∀ ps a, (ps, a) ∈ b.edges → a ∈ U :=
    fun ps a h => heads ps a (List.mem_append_left _ h)
  rw [resolution_strict_iff_close]
  have eb := close_exact U b.roots b.edges rb hb
  have ea := close_exact U (append b w).roots (append b w).edges roots heads
  constructor
  · rintro ⟨x, hx, hn, hq⟩
    exact ⟨x, hx, fun h => hn ((eb x).mpr h), (ea x).mp hq⟩
  · rintro ⟨x, hx, hn, hq⟩
    exact ⟨x, hx, fun h => hn ((eb x).mp h), (ea x).mpr hq⟩

/-- The complete account of one coordinate under append: never decreases,
and rises exactly on newly supported probes. -/
theorem resolution_exact (U : List A) (b w : Batch A)
    (roots : ∀ a, a ∈ (append b w).roots → a ∈ U)
    (heads : ∀ ps a, (ps, a) ∈ (append b w).edges → a ∈ U)
    (probes : Axis → List A) (i : Axis) :
    resolution probes (classify U b) i ≤ resolution probes (classify U (append b w)) i ∧
      (resolution probes (classify U b) i < resolution probes (classify U (append b w)) i ↔
        ∃ x, x ∈ probes i ∧ ¬ Knowledge (authority b) x ∧
          Knowledge (authority (append b w)) x) :=
  ⟨append_resolution_free U b w probes i, resolution_append_iff U b w roots heads probes i⟩

end Headline

/-! ### Controls: both domain premises of `resolution_append_iff` are needed

Each one dropped alone (the other still holding) makes the equivalence
false: the executable closure over-approximates and a coordinate rises with
no newly supported probe. -/

def unitProbe (xs : List Nat) : Unit → List Nat := fun _ => xs

theorem roots_premise_needed :
    let U : List Nat := [0]
    let b : Batch Nat := ⟨[], []⟩
    let w : Batch Nat := ⟨[5], []⟩
    (∀ ps a, (ps, a) ∈ (append b w).edges → a ∈ U) ∧
      ¬ (resolution (unitProbe [0]) (classify U b) () <
            resolution (unitProbe [0]) (classify U (append b w)) () ↔
          ∃ x, x ∈ unitProbe [0] () ∧ ¬ Knowledge (authority b) x ∧
            Knowledge (authority (append b w)) x) := by
  intro U b w
  refine ⟨fun _ _ h => by simp [w, b, append] at h, fun hiff => ?_⟩
  obtain ⟨x, hx, -, hk⟩ := hiff.mp (by decide)
  simp [unitProbe] at hx
  subst hx
  cases hk with
  | root hr => simp [authority, append, b, w] at hr
  | step hr _ => simp [authority, append, b, w] at hr

theorem heads_premise_needed :
    let U : List Nat := [0, 1]
    let b : Batch Nat := ⟨[0], []⟩
    let w : Batch Nat := ⟨[], [([0], 5)]⟩
    (∀ a, a ∈ (append b w).roots → a ∈ U) ∧
      ¬ (resolution (unitProbe [1]) (classify U b) () <
            resolution (unitProbe [1]) (classify U (append b w)) () ↔
          ∃ x, x ∈ unitProbe [1] () ∧ ¬ Knowledge (authority b) x ∧
            Knowledge (authority (append b w)) x) := by
  intro U b w
  refine ⟨fun a h => by simp [w, b, append, U] at h ⊢; exact Or.inl h, fun hiff => ?_⟩
  obtain ⟨x, hx, -, hk⟩ := hiff.mp (by decide)
  simp [unitProbe] at hx
  subst hx
  cases hk with
  | root hr => simp [authority, append, b, w] at hr
  | step hr _ => simp [authority, append, b, w] at hr

/-- Exactness is load-bearing for the abstract vector too: a classifier not
tied to the closure can make a coordinate drop on an append. -/
theorem inexact_classifier_can_drop :
    resolution (unitProbe [0, 1]) (fun _ : Nat => true) () >
      resolution (unitProbe [0, 1])
        (classify [0, 1] (append (⟨[0], []⟩ : Batch Nat) ⟨[], []⟩)) () := by
  decide

/-! ## Redundant appends, characterized exactly

`Hyperlattice.redundant` gives sufficient conditions.  They are also
necessary, so the statement is an equivalence: no weaker condition suffices
and no stronger conclusion exists. -/

section Redundant
variable {A : Type}

theorem redundant_iff (g w : Graph A) :
    (∀ a, Knowledge (join g w) a ↔ Knowledge g a) ↔
      ((∀ a, w.roots a → Knowledge g a) ∧ Closed w.edges (Knowledge g)) := by
  constructor
  · intro h
    refine ⟨fun a hw => (h a).mp (.root (Or.inr hw)), fun ps a he hp => (h a).mp ?_⟩
    exact .step (Or.inr he) (fun p hm => (h p).mpr (hp p hm))
  · exact fun ⟨r, e⟩ => redundant r e

end Redundant

def zeroGraph : Graph Nat := ⟨fun x => x = 0, fun _ _ => False⟩
def emptyGraph : Graph Nat := ⟨fun _ => False, fun _ _ => False⟩

theorem zero_knowledge (a : Nat) : Knowledge zeroGraph a ↔ a = 0 :=
  ⟨fun h => by cases h with | root hb => exact hb | step hr _ => exact hr.elim, fun h => .root h⟩

theorem empty_knowledge (a : Nat) : ¬ Knowledge emptyGraph a := fun h => by
  cases h with | root hb => exact hb | step hr _ => exact hr

/-- Root condition alone is not enough: an appended rule can add knowledge. -/
theorem redundant_needs_edges :
    let w : Graph Nat := ⟨fun _ => False, fun ps x => ps = [0] ∧ x = 1⟩
    (∀ a, w.roots a → Knowledge zeroGraph a) ∧
      ¬ (∀ a, Knowledge (join zeroGraph w) a ↔ Knowledge zeroGraph a) := by
  intro w
  refine ⟨fun _ h => h.elim, fun h => ?_⟩
  have k : Knowledge (join zeroGraph w) 1 :=
    .step (Or.inr ⟨rfl, rfl⟩) (fun p hp => by simp at hp; subst hp; exact .root (Or.inl rfl))
  exact absurd ((zero_knowledge 1).mp ((h 1).mp k)) (by decide)

/-- Edge condition alone is not enough: an appended root can add knowledge. -/
theorem redundant_needs_roots :
    let w : Graph Nat := ⟨fun x => x = 1, fun _ _ => False⟩
    Closed w.edges (Knowledge zeroGraph) ∧
      ¬ (∀ a, Knowledge (join zeroGraph w) a ↔ Knowledge zeroGraph a) := by
  intro w
  refine ⟨fun _ _ h _ => h.elim, fun h => ?_⟩
  exact absurd ((zero_knowledge 1).mp ((h 1).mp (.root (Or.inr rfl)))) (by decide)

/-! ## The abstract expansion vector keeps three premises, each needed

`Hyperlattice.expansion_vector` assumes the graph is extended and both
classifiers are exact.  Dropping any one, with the other two holding, lets a
coordinate fall. -/

def isZero (a : Nat) : Bool := a == 0

theorem zero_exact : Exact zeroGraph isZero := fun a => by
  rw [zero_knowledge]; simp [isZero]

theorem empty_exact : Exact emptyGraph (fun _ => false) := fun a =>
  ⟨fun h => Bool.noConfusion h, fun h => absurd h (empty_knowledge a)⟩

theorem expansion_needs_extension :
    Exact zeroGraph isZero ∧ Exact emptyGraph (fun _ => false) ∧
      ¬ (resolution (unitProbe [0]) isZero () ≤
          resolution (unitProbe [0]) (fun _ => false) ()) :=
  ⟨zero_exact, empty_exact, by decide⟩

theorem expansion_needs_old_exact :
    Extends emptyGraph emptyGraph ∧ Exact emptyGraph (fun _ => false) ∧
      ¬ (resolution (unitProbe [0]) (fun _ => true) () ≤
          resolution (unitProbe [0]) (fun _ => false) ()) :=
  ⟨⟨fun _ h => h, fun _ _ h => h⟩, empty_exact, by decide⟩

theorem expansion_needs_new_exact :
    Extends zeroGraph zeroGraph ∧ Exact zeroGraph isZero ∧
      ¬ (resolution (unitProbe [0]) isZero () ≤
          resolution (unitProbe [0]) (fun _ => false) ()) :=
  ⟨⟨fun _ h => h, fun _ _ h => h⟩, zero_exact, by decide⟩

/-! ## The merge, checked

The authority type is software-optimality's hypergraph and knowledge is its
`derives`, by definition, so the two developments share one object. -/

theorem graph_is_optimality_hypergraph :
    Graph Nat = HypergraphIncremental.Hypergraph Nat := rfl

theorem knowledge_is_derives {A : Type} (g : Graph A) (a : A) :
    Knowledge g a ↔ HypergraphIncremental.derives g a := Iff.rfl

#print axioms resolution_strict_iff_close
#print axioms resolution_append_iff
#print axioms resolution_exact
#print axioms roots_premise_needed
#print axioms heads_premise_needed
#print axioms inexact_classifier_can_drop
#print axioms redundant_iff
#print axioms redundant_needs_edges
#print axioms redundant_needs_roots
#print axioms expansion_needs_extension
#print axioms expansion_needs_old_exact
#print axioms expansion_needs_new_exact
#print axioms graph_is_optimality_hypergraph
#print axioms knowledge_is_derives
end Pareto
