import Hyperlattice
import ExecutableClosure

namespace WitnessExecutable
open Hyperlattice
variable {A : Type} [DecidableEq A]

/-- An append consists of admitted atoms and admitted hyperedges, not necessarily good news. -/
structure Batch (A : Type) where
  roots : List A
  edges : List (List A × A)

def authority (b : Batch A) : Graph A :=
  ⟨fun a => a ∈ b.roots, fun ps a => (ps,a) ∈ b.edges⟩
def append (b w : Batch A) : Batch A := ⟨b.roots ++ w.roots, b.edges ++ w.edges⟩

omit [DecidableEq A] in
theorem append_exact (b w : Batch A) : Same (authority (append b w)) (join (authority b) (authority w)) :=
  ⟨fun _ => List.mem_append, fun _ _ => List.mem_append⟩

def classify (U : List A) (b : Batch A) : A → Bool :=
  fun a => (ExecutableClosure.close U b.roots b.edges).contains a

theorem classifier_exact (U : List A) (b : Batch A)
    (roots : ∀ a, a ∈ b.roots → a ∈ U)
    (heads : ∀ ps a, (ps,a) ∈ b.edges → a ∈ U) :
    Exact (authority b) (classify U b) := by
  intro a
  simp only [classify, List.contains_iff]
  exact ExecutableClosure.close_exact U b.roots b.edges roots heads a

/-- Executable quantities link to graph semantics, including newly admitted rules. -/
theorem append_resolution {Axis : Type} (U : List A) (b w : Batch A)
    (roots : ∀ a, a ∈ (append b w).roots → a ∈ U)
    (heads : ∀ ps a, (ps,a) ∈ (append b w).edges → a ∈ U)
    (probes : Axis → List A) : ∀ i,
    resolution probes (classify U b) i ≤
      resolution probes (classify U (append b w)) i := by
  have rb : ∀ a, a ∈ b.roots → a ∈ U :=
    fun a h => roots a (List.mem_append_left _ h)
  have hb : ∀ ps a, (ps,a) ∈ b.edges → a ∈ U :=
    fun ps a h => heads ps a (List.mem_append_left _ h)
  exact expansion_vector
    ⟨fun _ h => List.mem_append_left _ h, fun _ _ h => List.mem_append_left _ h⟩
    _ _ (classifier_exact U b rb hb)
    (classifier_exact U (append b w) roots heads) probes

/-- A configuration catalogue is all subsets of resolved atoms; qualification may filter it.
    Count is of list entries; no-duplicate input makes those entries distinct subsets. -/
def configurations (U : List A) (b : Batch A) : List (List A) :=
  ExecutableClosure.subsets (ExecutableClosure.close U b.roots b.edges)

theorem configuration_count (U : List A) (b : Batch A) :
    (configurations U b).length =
      2 ^ (ExecutableClosure.close U b.roots b.edges).length :=
  ExecutableClosure.subsets_count _

omit [DecidableEq A] in
theorem count_eq_filter (p : A → Bool) (xs : List A) :
    Hyperlattice.count p xs = (xs.filter p).length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases hp : p x <;> simp [Hyperlattice.count, hp, ih, Nat.add_comm]

omit [DecidableEq A] in
theorem count_congr (p q : A → Bool) (xs : List A)
    (h : ∀ x, x ∈ xs → p x = q x) : Hyperlattice.count p xs = Hyperlattice.count q xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp [Hyperlattice.count, hx, ht]

theorem classified_count (U : List A) (b : Batch A) :
    Hyperlattice.count (classify U b) U = (ExecutableClosure.close U b.roots b.edges).length := by
  unfold classify ExecutableClosure.close
  rw [count_congr _ (fun a => (ExecutableClosure.models U b.roots b.edges).all
    (fun X => X.contains a)) U ?_]
  · exact count_eq_filter _ _
  · intro x hx
    apply Bool.eq_iff_iff.mpr
    simp [List.contains_iff, hx]

/-- Exact combinatorial multiplier: duplicates have delta 0 and factor 1.
    This counts catalogue entries, before the feasibility/qualification filter. -/
theorem catalogue_compounding (U : List A) (b w : Batch A)
    (roots : ∀ a, a ∈ (append b w).roots → a ∈ U)
    (heads : ∀ ps a, (ps,a) ∈ (append b w).edges → a ∈ U) :
    (configurations U (append b w)).length = (configurations U b).length *
      2 ^ ((ExecutableClosure.close U (append b w).roots (append b w).edges).length -
        (ExecutableClosure.close U b.roots b.edges).length) := by
  have hm := append_resolution U b w roots heads (fun _ : Unit => U) ()
  change Hyperlattice.count (classify U b) U ≤ Hyperlattice.count (classify U (append b w)) U at hm
  rw [classified_count, classified_count] at hm
  rw [configuration_count, configuration_count]
  have he : (ExecutableClosure.close U b.roots b.edges).length +
      ((ExecutableClosure.close U (append b w).roots (append b w).edges).length -
       (ExecutableClosure.close U b.roots b.edges).length) =
       (ExecutableClosure.close U (append b w).roots (append b w).edges).length := by omega
  exact (Nat.pow_add 2 _ _).symm.trans (congrArg (fun n => 2 ^ n) he) |>.symm

/-- An arbitrary total Boolean gate can be exhaustively and exactly selected. -/
def qualified (U : List A) (b : Batch A) (gate : List A → Bool) :=
  (configurations U b).filter gate

theorem qualification_exact (U : List A) (b : Batch A)
    (gate : List A → Bool) (c : List A) :
    c ∈ qualified U b gate ↔ c ∈ configurations U b ∧ gate c = true := by
  exact List.mem_filter

/-- Matrices are derived views: premise incidence and co-premise interaction. -/
def incidence (b : Batch A) (row : List A × A) (a : A) : Bool :=
  b.edges.contains row && row.1.contains a

def interaction (b : Batch A) (a c : A) : Bool :=
  b.edges.any (fun e => e.1.contains a && e.1.contains c)

/-- Withdrawal filters the live projection. The archived b is not modified. -/
def project (b : Batch A) (dead : A → Bool) (deadEdge : (List A × A) → Bool) : Batch A :=
  ⟨b.roots.filter (fun a => !dead a), b.edges.filter (fun e => !deadEdge e)⟩

omit [DecidableEq A] in
theorem projection_supported (b : Batch A) (dead : A → Bool)
    (deadEdge : (List A × A) → Bool) :
    ∀ a, Knowledge (authority (project b dead deadEdge)) a → Knowledge (authority b) a := by
  apply knowledge_monotone
  exact ⟨fun _ h => (List.mem_filter.mp h).1, fun _ _ h => (List.mem_filter.mp h).1⟩

#print axioms append_resolution
#print axioms classifier_exact
#print axioms configuration_count
#print axioms catalogue_compounding
#print axioms qualification_exact
#print axioms projection_supported
end WitnessExecutable
