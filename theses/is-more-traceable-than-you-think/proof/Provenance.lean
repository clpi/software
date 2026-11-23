import Traceability
import Projection

/-!
Audit recording of accepted completion publications through the original fold.

The original Derivation uses a characteristic SET of premises. This recording
view therefore uses occurrence nodes: (original owner task ID, slot), with slot
zero reserved for the head and slot j+1 for premise position j. The immutable
task table decodes each occurrence to its full original prerequisite ID. Order
and repeated uses are recovered exactly by decode_ordered. An occurrence is not
the prerequisite task's head node. This is not equality between the ordered
computation graph and the characteristic-set audit graph, and makes no closure
or reachability correspondence claim.

All types and bounds refer to one fixed finite immutable task-table snapshot.
Finite enumeration supplies derivation equality constructively. Accepted
completion supplies the event and witnessed head; the original recordLift and
return theorems then derive its exact recorded edge and source. No premise
asserts contribution, external causal truth, or completeness of real sensing.
-/
namespace Provenance
open Incremental

def capacity : List TaskKey → Nat
  | [] => 0
  | key :: rest => key.premises.length + capacity rest

abbrev Event (tasks : List TaskKey) := Fin tasks.length
abbrev Node (tasks : List TaskKey) := Event tasks × Fin (capacity tasks + 1)

theorem capacity_bounds {tasks : List TaskKey} {key : TaskKey} (member : key ∈ tasks) :
    key.premises.length ≤ capacity tasks := by
  induction tasks with
  | nil => cases member
  | cons first rest ih =>
    rcases List.mem_cons.mp member with same | later
    · subst key
      exact Nat.le_add_right _ _
    · have bound := ih later
      change key.premises.length ≤ first.premises.length + capacity rest
      omega

/-- Equality of every premise bit in the finite occurrence universe is tested. -/
def finiteDerivationEq (owners slots : Nat) :
    DecidableEq (Traceability.Derivation (Fin owners × Fin slots)) := fun a b =>
  if heads : a.head = b.head then
    if bits : ∀ owner : Fin owners, ∀ slot : Fin slots,
        a.premises (owner, slot) = b.premises (owner, slot) then
      .isTrue (by
        have premises : a.premises = b.premises := by
          funext node
          exact bits node.1 node.2
        cases a
        cases b
        simp only [Traceability.Derivation.mk.injEq] at *
        exact ⟨premises, heads⟩)
    else .isFalse (by
      intro same
      apply bits
      intro owner slot
      rw [same])
  else .isFalse (fun same => heads (congrArg Traceability.Derivation.head same))

instance (tasks : List TaskKey) : DecidableEq (Traceability.Derivation (Node tasks)) :=
  finiteDerivationEq tasks.length (capacity tasks + 1)

def head (tasks : List TaskKey) (event : Event tasks) : Node tasks :=
  (event, ⟨0, Nat.zero_lt_succ _⟩)

def occurrence (tasks : List TaskKey) (event : Event tasks)
    (position : Fin tasks[event.val].premises.length) : Node tasks :=
  (event, ⟨position.val + 1, by
    have bound := capacity_bounds (List.getElem_mem event.isLt)
    have within := position.isLt
    omega⟩)

def decode (tasks : List TaskKey) (node : Node tasks) : Option Nat :=
  if node.2.val = 0 then none else tasks[node.1.val].premises[node.2.val - 1]?

def record (tasks : List TaskKey) (event : Event tasks) : Traceability.Derivation (Node tasks) :=
  ⟨fun node => decide (node.1 = event ∧ 0 < node.2.val ∧
      node.2.val ≤ tasks[event.val].premises.length), head tasks event⟩

def lift (tasks : List TaskKey) : Event tasks → Traceability.Graph (Node tasks) :=
  Traceability.recordLift (record tasks)

def witnesses (tasks : List TaskKey) (origins : List Nat) : List (Event tasks) :=
  origins.filterMap (fun task => if bound : task < tasks.length then some ⟨task, bound⟩ else none)

theorem occurrence_decode (tasks : List TaskKey) (event : Event tasks)
    (position : Fin tasks[event.val].premises.length) :
    decode tasks (occurrence tasks event position) = some tasks[event.val].premises[position.val] := by
  change (if position.val + 1 = 0 then none else
    tasks[event.val].premises[position.val + 1 - 1]?) = _
  rw [if_neg (by omega), Nat.add_sub_cancel]
  exact List.getElem?_eq_some_iff.mpr ⟨position.isLt, rfl⟩

/-- Decoding every occurrence in position order returns the full original list. -/
theorem decode_ordered (tasks : List TaskKey) (event : Event tasks) :
    (List.ofFn (occurrence tasks event)).map (decode tasks) =
      tasks[event.val].premises.map some := by
  apply List.ext_getElem?
  intro index
  rw [List.getElem?_map, List.getElem?_ofFn, List.getElem?_map]
  by_cases bound : index < tasks[event.val].premises.length
  · rw [dif_pos bound, List.getElem?_eq_some_iff.mpr ⟨bound, rfl⟩]
    change some (decode tasks (occurrence tasks event ⟨index, bound⟩)) = _
    rw [occurrence_decode]
    rfl
  · rw [dif_neg bound, List.getElem?_eq_none (Nat.le_of_not_gt bound)]
    rfl

/-- Equal prerequisite IDs at different positions remain distinct occurrences. -/
theorem occurrence_position_injective (tasks : List TaskKey) (event : Event tasks)
    {left right : Fin tasks[event.val].premises.length}
    (same : occurrence tasks event left = occurrence tasks event right) : left = right := by
  have slots := congrArg (fun node : Node tasks => node.2.val) same
  change left.val + 1 = right.val + 1 at slots
  apply Fin.ext
  omega

theorem record_premises_exact (tasks : List TaskKey) (event : Event tasks) (node : Node tasks) :
    (record tasks event).premises node = true ↔
      ∃ position, node = occurrence tasks event position := by
  simp only [record, decide_eq_true_eq]
  constructor
  · rintro ⟨owner, positive, bound⟩
    let position : Fin tasks[event.val].premises.length := ⟨node.2.val - 1, by omega⟩
    refine ⟨position, Prod.ext owner ?_⟩
    apply Fin.ext
    change node.2.val = node.2.val - 1 + 1
    omega
  · rintro ⟨position, same⟩
    subst node
    refine ⟨rfl, ?_, ?_⟩
    · exact Nat.zero_lt_succ _
    · change position.val + 1 ≤ tasks[event.val].premises.length
      exact position.isLt

theorem witness_member (tasks : List TaskKey) (origins : List Nat) (event : Event tasks)
    (member : event.val ∈ origins) : event ∈ witnesses tasks origins := by
  apply List.mem_filterMap.mpr
  refine ⟨event.val, member, ?_⟩
  simp only [dif_pos event.isLt]

/-- The witnessed-head theorem is used; its selected owner must be this event. -/
theorem retained_return (tasks : List TaskKey) (origins : List Nat) (event : Event tasks)
    (member : event ∈ witnesses tasks origins) :
    (Traceability.fold (lift tasks) (witnesses tasks origins)).nodes (head tasks event) = true ∧
    (Traceability.fold (lift tasks) (witnesses tasks origins)).edges (record tasks event) = true ∧
    Traceability.contributor (lift tasks) (witnesses tasks origins) (record tasks event) = some event := by
  have witnessed : (Traceability.fold (lift tasks) (witnesses tasks origins)).nodes
      (head tasks event) = true :=
    (Traceability.fold_nodes (lift tasks)).mpr
      ⟨event, member, by simp [lift, Traceability.recordLift, record]⟩
  obtain ⟨selected, _, sameHead, recorded⟩ :=
    Traceability.returns_recorded_head (record tasks) witnessed
  have selectedEq : selected = event := congrArg Prod.fst sameHead
  subst selected
  obtain ⟨source, found, _, contributes⟩ :=
    Traceability.returns_recorded_edge_weaker (lift tasks) recorded
  have sameRecord : record tasks source = record tasks event := of_decide_eq_true contributes
  have sourceEq : source = event :=
    congrArg (fun d : Traceability.Derivation (Node tasks) => d.head.1) sameRecord
  subst source
  exact ⟨witnessed, recorded, found⟩

/-- Actual accepted completion derives the event and every recording conclusion. -/
theorem completed_return {Value : Type} (op : Scope → List Value → Value)
    (tasks : List TaskKey) {state next : Projection.State Value} {task : Nat}
    (accepted : Projection.complete op tasks state task = some next) :
    ∃ event : Event tasks, event.val = task ∧ event ∈ witnesses tasks next.origins ∧
      (Traceability.fold (lift tasks) (witnesses tasks next.origins)).nodes (head tasks event) = true ∧
      (Traceability.fold (lift tasks) (witnesses tasks next.origins)).edges (record tasks event) = true ∧
      Traceability.contributor (lift tasks) (witnesses tasks next.origins) (record tasks event) = some event := by
  obtain ⟨key, refs, values, table, _, _, _, _, nextEq⟩ := Projection.complete_spec op tasks accepted
  have bound := (List.getElem?_eq_some_iff.mp table).1
  let event : Event tasks := ⟨task, bound⟩
  have member : event ∈ witnesses tasks next.origins := by
    apply witness_member
    rw [nextEq]
    exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
  exact ⟨event, rfl, member, retained_return tasks next.origins event member⟩

theorem publish_origins {Value : Type} (op : Scope → List Value → Value)
    (tasks : List TaskKey) {state next : Projection.State Value} {order : List Nat}
    (accepted : Projection.publish op tasks state order = some next) :
    next.origins = state.origins ++ order := by
  induction order generalizing state with
  | nil =>
    simp only [Projection.publish, Option.some.injEq] at accepted
    subst next
    rw [List.append_nil]
  | cons task rest ih =>
    cases first : Projection.complete op tasks state task with
    | none => simp [Projection.publish, first] at accepted
    | some middle =>
      simp only [Projection.publish, first, Option.bind] at accepted
      obtain ⟨key, refs, values, _, _, _, _, _, middleEq⟩ := Projection.complete_spec op tasks first
      rw [ih accepted, middleEq]
      simp only [List.append_assoc, List.singleton_append]

theorem published_tasks_exist {Value : Type} (op : Scope → List Value → Value)
    (tasks : List TaskKey) {state next : Projection.State Value} {order : List Nat}
    (accepted : Projection.publish op tasks state order = some next) :
    ∀ task ∈ order, ∃ key, tasks[task]? = some key := by
  induction order generalizing state with
  | nil => intro task member; cases member
  | cons firstTask rest ih =>
    cases first : Projection.complete op tasks state firstTask with
    | none => simp [Projection.publish, first] at accepted
    | some middle =>
      simp only [Projection.publish, first, Option.bind] at accepted
      intro task member
      rcases List.mem_cons.mp member with same | later
      · subst task
        obtain ⟨key, refs, values, table, _⟩ := Projection.complete_spec op tasks first
        exact ⟨key, table⟩
      · exact ih accepted task later

/-- Every task in an accepted publication schedule has its original record back. -/
theorem published_return {Value : Type} (op : Scope → List Value → Value)
    (tasks : List TaskKey) {next : Projection.State Value} {order : List Nat}
    (accepted : Projection.publish op tasks Projection.empty order = some next)
    {task : Nat} (scheduled : task ∈ order) :
    ∃ event : Event tasks, event.val = task ∧ event ∈ witnesses tasks next.origins ∧
      (Traceability.fold (lift tasks) (witnesses tasks next.origins)).nodes (head tasks event) = true ∧
      (Traceability.fold (lift tasks) (witnesses tasks next.origins)).edges (record tasks event) = true ∧
      Traceability.contributor (lift tasks) (witnesses tasks next.origins) (record tasks event) = some event := by
  obtain ⟨key, table⟩ := published_tasks_exist op tasks accepted task scheduled
  let event : Event tasks := ⟨task, (List.getElem?_eq_some_iff.mp table).1⟩
  have member : event ∈ witnesses tasks next.origins := by
    apply witness_member
    rw [publish_origins op tasks accepted]
    exact scheduled
  exact ⟨event, rfl, member, retained_return tasks next.origins event member⟩

end Provenance
