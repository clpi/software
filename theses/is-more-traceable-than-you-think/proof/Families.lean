import Pipeline

/-!
Independent component coordinates share a read-only environment. Each coordinate
chooses an already checked program. The product represents choices without
materializing them. It introduces no cross-coordinate rule or effect. Assignment
counts do not imply distinct output values; distinctness below concerns Boolean
selector tuples only.
-/
namespace Families
open Pipeline

structure Component where
  rows : List Row
  output : Nat

def checked (component : Component) : Bool :=
  check 0 component.rows && decide (component.output < component.rows.length)

def sourceComponent (env : Environment) (component : Component) : Option Int :=
  (source env [] component.rows).bind (fun values => values[component.output]?)

def targetComponent (env : Environment) (component : Component) : Option Int :=
  (target env [] component.rows).bind (fun values => values[component.output]?)

def sourceTuple (env : Environment) : List Component → Option (List Int)
  | [] => some []
  | component :: rest => (sourceComponent env component).bind
      (fun value => (sourceTuple env rest).map (value :: ·))

def targetTuple (env : Environment) : List Component → Option (List Int)
  | [] => some []
  | component :: rest => (targetComponent env component).bind
      (fun value => (targetTuple env rest).map (value :: ·))

def assignments {α : Type} : List (List α) → List (List α)
  | [] => [[]]
  | alternatives :: rest =>
    alternatives.flatMap (fun choice => (assignments rest).map (choice :: ·))

def assignmentCount {α : Type} : List (List α) → Nat
  | [] => 1
  | alternatives :: rest => alternatives.length * assignmentCount rest

def storedReferences {α : Type} : List (List α) → Nat
  | [] => 0
  | alternatives :: rest => alternatives.length + storedReferences rest

def binaryTuples : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (binaryTuples n).map (false :: ·) ++ (binaryTuples n).map (true :: ·)

theorem checked_component_correct {component : Component}
    (accepted : checked component = true) (env : Environment) :
    ∃ value, sourceComponent env component = some value ∧ targetComponent env component = some value := by
  have parts : check 0 component.rows = true ∧ component.output < component.rows.length := by
    simpa only [checked, Bool.and_eq_true, decide_eq_true_eq] using accepted
  obtain ⟨values, src, tgt, length⟩ := checked_program_correct parts.1 env
  have bound : component.output < values.length := by rw [length]; exact parts.2
  refine ⟨values[component.output], ?_, ?_⟩
  · simp only [sourceComponent, src, Option.bind]
    exact List.getElem?_eq_some_iff.mpr ⟨bound, rfl⟩
  · simp only [targetComponent, tgt, Option.bind]
    exact List.getElem?_eq_some_iff.mpr ⟨bound, rfl⟩

theorem independent_tuple_correct {components : List Component}
    (accepted : ∀ component ∈ components, checked component = true) (env : Environment) :
    ∃ values, sourceTuple env components = some values ∧
      targetTuple env components = some values ∧ values.length = components.length := by
  induction components with
  | nil => exact ⟨[], rfl, rfl, rfl⟩
  | cons component rest ih =>
    obtain ⟨value, src, tgt⟩ := checked_component_correct
      (accepted component List.mem_cons_self) env
    obtain ⟨values, srcs, tgts, length⟩ := ih
      (fun c member => accepted c (List.mem_cons_of_mem _ member))
    refine ⟨value :: values, ?_, ?_, ?_⟩
    · simp only [sourceTuple, src, srcs, Option.bind, Option.map]
    · simp only [targetTuple, tgt, tgts, Option.bind, Option.map]
    · simp only [List.length_cons, length]

theorem flatMap_constant_length {α β : Type} (items : List α) (f : α → List β)
    (count : Nat) (lengths : ∀ item ∈ items, (f item).length = count) :
    (items.flatMap f).length = items.length * count := by
  induction items with
  | nil => simp only [List.flatMap_nil, List.length_nil, Nat.zero_mul]
  | cons item rest ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons,
      lengths item List.mem_cons_self,
      ih (fun x member => lengths x (List.mem_cons_of_mem _ member)), Nat.succ_mul]
    omega

theorem assignment_count_exact {α : Type} (factors : List (List α)) :
    (assignments factors).length = assignmentCount factors := by
  induction factors with
  | nil => rfl
  | cons alternatives rest ih =>
    unfold assignments assignmentCount
    apply flatMap_constant_length
    intro choice _
    simp only [List.length_map, ih]

theorem selected_length {α : Type} {factors : List (List α)} {selected : List α}
    (member : selected ∈ assignments factors) : selected.length = factors.length := by
  induction factors generalizing selected with
  | nil =>
    have same : selected = [] := List.mem_singleton.mp member
    subst selected
    rfl
  | cons alternatives rest ih =>
    obtain ⟨choice, _, selectedMember⟩ := List.mem_flatMap.mp member
    obtain ⟨tail, tailMember, same⟩ := List.mem_map.mp selectedMember
    subst selected
    simp only [List.length_cons, ih tailMember]

theorem selected_member {α : Type} {factors : List (List α)} {selected : List α}
    (selection : selected ∈ assignments factors) {item : α} (member : item ∈ selected) :
    ∃ alternatives ∈ factors, item ∈ alternatives := by
  induction factors generalizing selected with
  | nil =>
    have same : selected = [] := List.mem_singleton.mp selection
    subst selected
    cases member
  | cons alternatives rest ih =>
    obtain ⟨choice, choiceMember, selectedMember⟩ := List.mem_flatMap.mp selection
    obtain ⟨tail, tailMember, same⟩ := List.mem_map.mp selectedMember
    subst selected
    rcases List.mem_cons.mp member with first | later
    · subst item
      exact ⟨alternatives, List.mem_cons_self, choiceMember⟩
    · obtain ⟨choices, choicesMember, itemMember⟩ := ih tailMember later
      exact ⟨choices, List.mem_cons_of_mem _ choicesMember, itemMember⟩

theorem every_selection_correct {factors : List (List Component)}
    (accepted : ∀ alternatives ∈ factors, ∀ component ∈ alternatives, checked component = true)
    {selected : List Component} (selection : selected ∈ assignments factors) (env : Environment) :
    ∃ values, sourceTuple env selected = some values ∧ targetTuple env selected = some values ∧
      values.length = factors.length := by
  obtain ⟨values, src, tgt, length⟩ := independent_tuple_correct (components := selected) (by
    intro component member
    obtain ⟨alternatives, factorMember, componentMember⟩ := selected_member selection member
    exact accepted alternatives factorMember component componentMember) env
  exact ⟨values, src, tgt, length.trans (selected_length selection)⟩

theorem repeated_factor_count {α : Type} (alternatives : List α) (count : Nat) :
    assignmentCount (List.replicate count alternatives) = alternatives.length ^ count := by
  induction count with
  | zero => rfl
  | succ n ih =>
    simp only [List.replicate_succ, assignmentCount, ih, Nat.pow_succ, Nat.mul_comm]

theorem binary_assignment_count {α : Type} (left right : α) (count : Nat) :
    (assignments (List.replicate count [left, right])).length = 2 ^ count := by
  rw [assignment_count_exact, repeated_factor_count]
  rfl

theorem binary_stored_references {α : Type} (left right : α) (count : Nat) :
    storedReferences (List.replicate count [left, right]) = 2 * count := by
  induction count with
  | zero => rfl
  | succ n ih =>
    simp only [List.replicate_succ, storedReferences, List.length_cons, List.length_nil, ih,
      Nat.mul_succ]
    omega

theorem binaryTuples_assignments (count : Nat) :
    binaryTuples count = assignments (List.replicate count [false, true]) := by
  induction count with
  | zero => rfl
  | succ n ih =>
    simp only [binaryTuples, ih, List.replicate_succ, assignments,
      List.flatMap_cons, List.flatMap_nil, List.append_nil]

theorem prefix_preserves_nodup {α : Type} (item : α) {tuples : List (List α)}
    (distinct : tuples.Nodup) : (tuples.map (item :: ·)).Nodup := by
  apply List.pairwise_map.mpr
  apply distinct.imp
  intro left right different same
  exact different (List.cons.inj same).2

theorem binaryTuples_nodup (count : Nat) : (binaryTuples count).Nodup := by
  induction count with
  | zero => exact List.Pairwise.cons (by simp) List.Pairwise.nil
  | succ n ih =>
    apply List.pairwise_append.mpr
    refine ⟨prefix_preserves_nodup false ih, prefix_preserves_nodup true ih, ?_⟩
    intro left leftMember right rightMember same
    obtain ⟨a, _, aEq⟩ := List.mem_map.mp leftMember
    obtain ⟨b, _, bEq⟩ := List.mem_map.mp rightMember
    have impossible : false :: a = true :: b := aEq.trans (same.trans bEq.symm)
    cases (List.cons.inj impossible).1

theorem binary_compact_distinct (count : Nat) :
    (binaryTuples count).Nodup ∧ (binaryTuples count).length = 2 ^ count ∧
      storedReferences (List.replicate count [false, true]) = 2 * count := by
  refine ⟨binaryTuples_nodup count, ?_, binary_stored_references false true count⟩
  rw [binaryTuples_assignments]
  exact binary_assignment_count false true count

theorem binary_component_family_correct (left right : Component)
    (leftChecked : checked left = true) (rightChecked : checked right = true) (count : Nat) :
    (assignments (List.replicate count [left, right])).length = 2 ^ count ∧
    storedReferences (List.replicate count [left, right]) = 2 * count ∧
    ∀ selected ∈ assignments (List.replicate count [left, right]), ∀ env,
      ∃ values, sourceTuple env selected = some values ∧ targetTuple env selected = some values ∧
        values.length = count := by
  refine ⟨binary_assignment_count left right count, binary_stored_references left right count, ?_⟩
  intro selected selection env
  have accepted : ∀ alternatives ∈ List.replicate count [left, right],
      ∀ component ∈ alternatives, checked component = true := by
    intro alternatives factorMember component member
    have alternativesEq := (List.mem_replicate.mp factorMember).2
    subst alternatives
    rcases List.mem_cons.mp member with same | tail
    · subst component; exact leftChecked
    · have same := List.mem_singleton.mp tail
      subst component; exact rightChecked
  obtain ⟨values, src, tgt, length⟩ := every_selection_correct accepted selection env
  exact ⟨values, src, tgt, by simpa only [List.length_replicate] using length⟩

end Families
