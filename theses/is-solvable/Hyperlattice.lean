import Std
import Qualification
import HypergraphIncremental
import ClosureStrength

namespace Hyperlattice
universe v
variable {A : Type}

/-- The sole authority: scoped support atoms and certified conjunctive hyperedges.
    This is software-optimality's `HypergraphIncremental.Hypergraph`, not a copy of it. -/
abbrev Graph (A : Type) := HypergraphIncremental.Hypergraph A

def join (g h : Graph A) : Graph A :=
  ⟨fun a => g.roots a ∨ h.roots a, fun ps a => g.edges ps a ∨ h.edges ps a⟩
def Knowledge (g : Graph A) : A → Prop := HypergraphIncremental.derives g
def Extends (g h : Graph A) : Prop :=
  (∀ a, g.roots a → h.roots a) ∧ (∀ ps a, g.edges ps a → h.edges ps a)
def Same (g h : Graph A) : Prop :=
  (∀ a, g.roots a ↔ h.roots a) ∧ (∀ ps a, g.edges ps a ↔ h.edges ps a)

theorem join_extends (g h : Graph A) : Extends g (join g h) :=
  ⟨fun _ h => Or.inl h, fun _ _ h => Or.inl h⟩
theorem knowledge_monotone {g h : Graph A} (e : Extends g h) :
    ∀ a, Knowledge g a → Knowledge h a := Qualification.monotone e.1 e.2

theorem same_knowledge {g h : Graph A} (e : Same g h) :
    ∀ a, Knowledge g a ↔ Knowledge h a := fun a =>
  ⟨knowledge_monotone ⟨fun x => (e.1 x).mp, fun ps x => (e.2 ps x).mp⟩ a,
   knowledge_monotone ⟨fun x => (e.1 x).mpr, fun ps x => (e.2 ps x).mpr⟩ a⟩

theorem join_comm (g h : Graph A) : Same (join g h) (join h g) :=
  ⟨fun _ => or_comm, fun _ _ => or_comm⟩
theorem join_assoc (g h k : Graph A) : Same (join (join g h) k) (join g (join h k)) :=
  ⟨fun _ => or_assoc, fun _ _ => or_assoc⟩
theorem duplicate (g : Graph A) : Same (join g g) g :=
  ⟨fun _ => ⟨fun h => h.elim id id, Or.inl⟩,
   fun _ _ => ⟨fun h => h.elim id id, Or.inl⟩⟩

def saturate (g : Graph A) : Graph A := ⟨Knowledge g, g.edges⟩
/-- Saturated caches are views. Joining them requires reclosure for cross-source rules. -/
theorem compounding (g h : Graph A) (a : A) :
    Knowledge (join g h) a ↔ Knowledge (join (saturate g) (saturate h)) a :=
  ClosureStrength.compounding_sources g.roots h.roots g.edges h.edges a

/-- A newly appended batch already justified by the old graph adds no knowledge. -/
theorem redundant {g w : Graph A}
    (roots : ∀ a, w.roots a → Knowledge g a)
    (edges : Qualification.Closed w.edges (Knowledge g)) :
    ∀ a, Knowledge (join g w) a ↔ Knowledge g a := by
  intro a; constructor
  · apply Qualification.least
    · intro x hx; exact hx.elim Qualification.Derives.root (roots x)
    · intro ps x he hp
      exact he.elim (fun h => Qualification.Derives.step h hp) (fun h => edges ps x h hp)
  · exact knowledge_monotone (join_extends g w) a

/-- Explicit finite probes define the resolution axes. Count unique probes for cardinality. -/
def count (p : A → Bool) : List A → Nat
  | [] => 0
  | x :: xs => (if p x then 1 else 0) + count p xs

theorem count_monotone (p q : A → Bool) (xs : List A)
    (h : ∀ x, x ∈ xs → p x = true → q x = true) : count p xs ≤ count q xs := by
  induction xs with
  | nil => simp [count]
  | cons x xs ih =>
    have ht := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    have hx := h x (by simp)
    cases hp : p x <;> cases hq : q x <;> simp_all [count] <;> omega

theorem count_strict (p q : A → Bool) (xs : List A)
    (h : ∀ x, x ∈ xs → p x = true → q x = true)
    (novel : ∃ x, x ∈ xs ∧ p x = false ∧ q x = true) : count p xs < count q xs := by
  induction xs with
  | nil => simp at novel
  | cons x xs ih =>
    have ht := count_monotone p q xs (fun y hy => h y (by simp [hy]))
    have hx := h x (by simp)
    obtain ⟨y, hy, hp, hq⟩ := novel
    rcases List.mem_cons.mp hy with he | he
    · subst y; simp [count, hp, hq]; omega
    · have hs := ih (fun y hy => h y (by simp [hy])) ⟨y, he, hp, hq⟩
      cases px : p x <;> cases qx : q x <;> simp_all [count] <;> omega

theorem count_strict_iff (p q : A → Bool) (xs : List A)
    (h : ∀ x, x ∈ xs → p x = true → q x = true) :
    count p xs < count q xs ↔ ∃ x, x ∈ xs ∧ p x = false ∧ q x = true := by
  constructor
  · intro hs
    classical
    apply Classical.byContradiction
    intro hn
    have rev : count q xs ≤ count p xs := by
      apply count_monotone
      intro x hx hq
      cases hp : p x
      · exact False.elim (hn ⟨x, hx, hp, hq⟩)
      · rfl
    omega
  · exact count_strict p q xs h

/-- The exact per-axis increment is nonnegative and telescopes under extension. -/
theorem count_delta (p q : A → Bool) (xs : List A)
    (h : ∀ x, x ∈ xs → p x = true → q x = true) :
    count p xs + (count q xs - count p xs) = count q xs := by
  have hm := count_monotone p q xs h
  omega

variable {Axis : Type v}
def resolution (probes : Axis → List A) (classified : A → Bool) : Axis → Nat :=
  fun i => count classified (probes i)

/-- Exact evaluated classifiers must be linked to the authority, not guessed. -/
def Exact (g : Graph A) (classified : A → Bool) : Prop :=
  ∀ a, classified a = true ↔ Knowledge g a

theorem expansion_vector {g h : Graph A} (extension : Extends g h)
    (p q : A → Bool) (ep : Exact g p) (eq : Exact h q)
    (probes : Axis → List A) :
    ∀ i, resolution probes p i ≤ resolution probes q i := by
  intro i; apply count_monotone
  intro x _ hx
  exact (eq x).mpr (knowledge_monotone extension x ((ep x).mp hx))

theorem strict_expansion {g h : Graph A} (extension : Extends g h)
    (p q : A → Bool) (ep : Exact g p) (eq : Exact h q)
    (probes : Axis → List A) (i : Axis)
    (novel : ∃ x, x ∈ probes i ∧ ¬ Knowledge g x ∧ Knowledge h x) :
    resolution probes p i < resolution probes q i := by
  apply count_strict
  · intro x _ hx; exact (eq x).mpr (knowledge_monotone extension x ((ep x).mp hx))
  · obtain ⟨x, hx, hn, hy⟩ := novel
    refine ⟨x, hx, ?_, (eq x).mpr hy⟩
    cases hp : p x
    · rfl
    · exact False.elim (hn ((ep x).mp hp))

/-- Projection filters supports and edges; append-only authority is untouched. -/
def live (g : Graph A) (dead : A → Prop) (deadEdge : List A → A → Prop) : Graph A :=
  ⟨fun a => g.roots a ∧ ¬ dead a, fun ps a => g.edges ps a ∧ ¬ deadEdge ps a⟩
theorem live_supported (g : Graph A) (dead : A → Prop) (de : List A → A → Prop) :
    ∀ a, Knowledge (live g dead de) a → Knowledge g a :=
  Qualification.withdrawal_no_new_support g.roots dead g.edges de

/-- Qualification exposes both polarities; conflict is not silently resolved. -/
def color (positive negative : Bool) : Nat :=
  (if positive then 1 else 0) + (if negative then 2 else 0)

#print axioms compounding
#print axioms expansion_vector
#print axioms strict_expansion
#print axioms redundant
end Hyperlattice
