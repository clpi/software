import Incremental

/-!
Original intern IDs and compact completion indices are different namespaces.
This projection preserves every ordered premise position, including repetition.
Completion checks readiness in the compact rows, then appends one immutable row.
The recording order may differ from original ID order.
-/
namespace Projection
open Incremental

def position : List Nat → Nat → Option Nat
  | [], _ => none
  | origin :: rest, task =>
    if origin = task then some 0 else (position rest task).map Nat.succ

def remap (origins : List Nat) : List Nat → Option (List Nat)
  | [] => some []
  | task :: rest =>
    match position origins task, remap origins rest with
    | some index, some indices => some (index :: indices)
    | _, _ => none

def readOrigin {Value : Type} (origins : List Nat) (rows : Cache Value)
    (task : Nat) : Option Value :=
  (position origins task).bind (fun index => rows[index]?.map Entry.value)

def gatherOrigins {Value : Type} (origins : List Nat) (rows : Cache Value) :
    List Nat → Option (List Value)
  | [] => some []
  | task :: rest =>
    match readOrigin origins rows task, gatherOrigins origins rows rest with
    | some value, some values => some (value :: values)
    | _, _ => none

theorem position_sound {origins : List Nat} {task index : Nat}
    (found : position origins task = some index) : origins[index]? = some task := by
  induction origins generalizing index with
  | nil => simp [position] at found
  | cons origin rest ih =>
    by_cases same : origin = task
    · simp only [position, same, if_true, Option.some.injEq] at found
      subst index
      simp only [List.getElem?_cons_zero, same]
    · cases tail : position rest task with
      | none => simp [position, same, tail] at found
      | some prior =>
        simp only [position, same, if_false, tail, Option.map, Option.some.injEq] at found
        subst index
        exact ih tail

theorem position_injective {origins : List Nat} {left right index : Nat}
    (first : position origins left = some index)
    (second : position origins right = some index) : left = right := by
  have a := position_sound first
  have b := position_sound second
  rw [a] at b
  exact Option.some.inj b

theorem position_append {origins : List Nat} {task index : Nat}
    (found : position origins task = some index) (more : List Nat) :
    position (origins ++ more) task = some index := by
  induction origins generalizing index with
  | nil => simp [position] at found
  | cons origin rest ih =>
    by_cases same : origin = task
    · simp only [position, same, if_true] at found
      simpa only [List.cons_append, position, same, if_true] using found
    · cases tail : position rest task with
      | none => simp [position, same, tail] at found
      | some prior =>
        simp only [position, same, if_false, tail, Option.map, Option.some.injEq] at found
        subst index
        simp only [List.cons_append, position, same, if_false, ih tail, Option.map]

theorem remap_append {origins tasks indices : List Nat}
    (mapped : remap origins tasks = some indices) (more : List Nat) :
    remap (origins ++ more) tasks = some indices := by
  induction tasks generalizing indices with
  | nil => exact mapped
  | cons task rest ih =>
    cases found : position origins task with
    | none => simp [remap, found] at mapped
    | some index =>
      cases tail : remap origins rest with
      | none => simp [remap, found, tail] at mapped
      | some refs =>
        simp only [remap, found, tail, Option.some.injEq] at mapped
        subst indices
        simp only [remap, position_append found more, ih tail]

theorem resolve_remap {Value : Type} (origins : List Nat) (rows : Cache Value)
    {tasks indices : List Nat} (mapped : remap origins tasks = some indices) :
    gatherOrigins origins rows tasks = resolve rows indices := by
  induction tasks generalizing indices with
  | nil =>
    have same : indices = [] := by simpa only [remap, Option.some.injEq] using mapped.symm
    subst indices
    rfl
  | cons task rest ih =>
    cases found : position origins task with
    | none => simp [remap, found] at mapped
    | some index =>
      cases tail : remap origins rest with
      | none => simp [remap, found, tail] at mapped
      | some refs =>
        simp only [remap, found, tail, Option.some.injEq] at mapped
        subst indices
        simp only [gatherOrigins, readOrigin, found, Option.bind, ih tail, resolve]
        cases rows[index]? <;> cases resolve rows refs <;> rfl

theorem remap_length {origins tasks indices : List Nat}
    (mapped : remap origins tasks = some indices) : indices.length = tasks.length := by
  induction tasks generalizing indices with
  | nil => simp [remap] at mapped; subst indices; rfl
  | cons task rest ih =>
    cases found : position origins task with
    | none => simp [remap, found] at mapped
    | some index =>
      cases tail : remap origins rest with
      | none => simp [remap, found, tail] at mapped
      | some refs =>
        simp only [remap, found, tail, Option.some.injEq] at mapped
        subst indices
        simp only [List.length_cons, ih tail]

theorem remap_injective {origins left right indices : List Nat}
    (first : remap origins left = some indices)
    (second : remap origins right = some indices) : left = right := by
  induction left generalizing right indices with
  | nil =>
    have zero : indices = [] := by simpa only [remap, Option.some.injEq] using first.symm
    have len := remap_length second
    rw [zero] at len
    exact (List.length_eq_zero_iff.mp len.symm).symm
  | cons task rest ih =>
    cases found : position origins task with
    | none => simp [remap, found] at first
    | some index =>
      cases tail : remap origins rest with
      | none => simp [remap, found, tail] at first
      | some refs =>
        simp only [remap, found, tail, Option.some.injEq] at first
        subst indices
        cases right with
        | nil => simp [remap] at second
        | cons other remaining =>
          cases otherFound : position origins other with
          | none => simp [remap, otherFound] at second
          | some otherIndex =>
            cases otherTail : remap origins remaining with
            | none => simp [remap, otherFound, otherTail] at second
            | some otherRefs =>
              simp only [remap, otherFound, otherTail, Option.some.injEq, List.cons.injEq] at second
              obtain ⟨headEq, tailEq⟩ := second
              subst otherIndex
              subst otherRefs
              rw [position_injective found otherFound, ih tail otherTail]

theorem remapped_keys_reflect_equality {origins : List Nat} {left right : TaskKey}
    {leftRefs rightRefs : List Nat}
    (first : remap origins left.premises = some leftRefs)
    (second : remap origins right.premises = some rightRefs)
    (same : (⟨left.scope, leftRefs⟩ : TaskKey) = ⟨right.scope, rightRefs⟩) : left = right := by
  have scopes := congrArg TaskKey.scope same
  have refs := congrArg TaskKey.premises same
  change leftRefs = rightRefs at refs
  rw [refs] at first
  have premises := remap_injective first second
  cases left
  cases right
  simp only [TaskKey.mk.injEq] at *
  exact ⟨scopes, premises⟩

theorem position_exists {origins : List Nat} {task : Nat} (member : task ∈ origins) :
    ∃ index, position origins task = some index := by
  induction origins with
  | nil => cases member
  | cons origin rest ih =>
    by_cases same : origin = task
    · exact ⟨0, by simp only [position, same, if_true]⟩
    · have later : task ∈ rest := (List.mem_cons.mp member).resolve_left (Ne.symm same)
      obtain ⟨index, found⟩ := ih later
      exact ⟨index + 1, by simp only [position, same, if_false, found, Option.map]⟩

theorem position_none {origins : List Nat} {task : Nat} :
    position origins task = none ↔ task ∉ origins := by
  constructor
  · intro absent member
    obtain ⟨index, found⟩ := position_exists member
    rw [absent] at found
    cases found
  · intro absent
    cases found : position origins task with
    | none => rfl
    | some index => exact False.elim (absent (List.mem_of_getElem? (position_sound found)))

theorem position_new {origins : List Nat} {task : Nat}
    (absent : position origins task = none) :
    position (origins ++ [task]) task = some origins.length := by
  induction origins with
  | nil => simp [position]
  | cons origin rest ih =>
    have noHead : origin ≠ task := by
      intro same
      simp only [position, same, if_true] at absent
      cases absent
    have noTail : position rest task = none := by
      cases found : position rest task with
      | none => rfl
      | some index => simp [position, noHead, found] at absent
    simp only [List.cons_append, position, noHead, if_false, ih noTail,
      Option.map, List.length_cons]

structure State (Value : Type) where
  origins : List Nat
  rows : Cache Value

def empty {Value : Type} : State Value := ⟨[], []⟩

def complete {Value : Type} (op : Scope → List Value → Value)
    (tasks : List TaskKey) (state : State Value) (task : Nat) : Option (State Value) :=
  match tasks[task]?, position state.origins task with
  | some key, none =>
    match remap state.origins key.premises with
    | none => none
    | some refs =>
      let projected : TaskKey := ⟨key.scope, refs⟩
      match lookup state.rows projected, resolve state.rows refs with
      | none, some values =>
        some ⟨state.origins ++ [task], state.rows ++ [⟨projected, op key.scope values⟩]⟩
      | _, _ => none
  | _, _ => none

def publish {Value : Type} (op : Scope → List Value → Value)
    (tasks : List TaskKey) (state : State Value) : List Nat → Option (State Value)
  | [] => some state
  | task :: rest => (complete op tasks state task).bind (fun next => publish op tasks next rest)

theorem complete_spec {Value : Type} (op : Scope → List Value → Value)
    (tasks : List TaskKey) {state next : State Value} {task : Nat}
    (accepted : complete op tasks state task = some next) :
    ∃ key refs values, tasks[task]? = some key ∧ position state.origins task = none ∧
      remap state.origins key.premises = some refs ∧
      lookup state.rows ⟨key.scope, refs⟩ = none ∧
      resolve state.rows refs = some values ∧
      next = ⟨state.origins ++ [task], state.rows ++ [⟨⟨key.scope, refs⟩, op key.scope values⟩]⟩ := by
  cases table : tasks[task]? with
  | none => simp [complete, table] at accepted
  | some key =>
    cases already : position state.origins task with
    | some index => simp [complete, table, already] at accepted
    | none =>
      cases mapped : remap state.origins key.premises with
      | none => simp [complete, table, already, mapped] at accepted
      | some refs =>
        cases found : lookup state.rows ⟨key.scope, refs⟩ with
        | some entry => simp [complete, table, already, mapped, found] at accepted
        | none =>
          cases ready : resolve state.rows refs with
          | none => simp [complete, table, already, mapped, found, ready] at accepted
          | some values =>
            simp only [complete, table, already, mapped, found, ready, Option.some.injEq] at accepted
            exact ⟨key, refs, values, rfl, rfl, mapped, found, ready, accepted.symm⟩

theorem complete_uses_original_dependencies {Value : Type}
    (op : Scope → List Value → Value) (tasks : List TaskKey)
    {state next : State Value} {task : Nat}
    (accepted : complete op tasks state task = some next) :
    ∃ key refs values, tasks[task]? = some key ∧
      remap state.origins key.premises = some refs ∧
      gatherOrigins state.origins state.rows key.premises = some values ∧
      next.rows = state.rows ++ [⟨⟨key.scope, refs⟩, op key.scope values⟩] := by
  obtain ⟨key, refs, values, table, _, mapped, _, ready, same⟩ := complete_spec op tasks accepted
  exact ⟨key, refs, values, table, mapped,
    (resolve_remap state.origins state.rows mapped).trans ready, congrArg State.rows same⟩

theorem complete_valid {Value : Type} (op : Scope → List Value → Value)
    (tasks : List TaskKey) {state next : State Value} {task : Nat}
    (prior : ValidLog op state.rows) (accepted : complete op tasks state task = some next) :
    ValidLog op next.rows := by
  obtain ⟨key, refs, values, _, _, _, fresh, ready, same⟩ := complete_spec op tasks accepted
  rw [same]
  exact .append prior fresh ready

theorem complete_length {Value : Type} (op : Scope → List Value → Value)
    (tasks : List TaskKey) {state next : State Value} {task : Nat}
    (sameLength : state.origins.length = state.rows.length)
    (accepted : complete op tasks state task = some next) : next.origins.length = next.rows.length := by
  obtain ⟨key, refs, values, _, _, _, _, _, same⟩ := complete_spec op tasks accepted
  rw [same]
  simp only [List.length_append, List.length_singleton, sameLength]

theorem complete_origins_unique {Value : Type} (op : Scope → List Value → Value)
    (tasks : List TaskKey) {state next : State Value} {task : Nat}
    (prior : state.origins.Nodup) (accepted : complete op tasks state task = some next) :
    next.origins.Nodup := by
  obtain ⟨key, refs, values, _, absent, _, _, _, same⟩ := complete_spec op tasks accepted
  rw [same]
  apply List.pairwise_append.mpr
  refine ⟨prior, by simp, ?_⟩
  intro old oldMember new newMember
  have newEq := List.mem_singleton.mp newMember
  subst new
  intro equal
  subst old
  exact position_none.mp absent oldMember

theorem complete_publishes_result {Value : Type} (op : Scope → List Value → Value)
    (tasks : List TaskKey) {state next : State Value} {task : Nat}
    (sameLength : state.origins.length = state.rows.length)
    (accepted : complete op tasks state task = some next) :
    ∃ key values, tasks[task]? = some key ∧
      gatherOrigins state.origins state.rows key.premises = some values ∧
      readOrigin next.origins next.rows task = some (op key.scope values) := by
  obtain ⟨key, refs, values, table, absent, mapped, _, ready, same⟩ := complete_spec op tasks accepted
  refine ⟨key, values, table, (resolve_remap state.origins state.rows mapped).trans ready, ?_⟩
  rw [same]
  simp only [readOrigin, position_new absent, sameLength, List.getElem?_concat_length,
    Option.bind, Option.map]

theorem publish_valid {Value : Type} (op : Scope → List Value → Value)
    (tasks : List TaskKey) {state next : State Value} {order : List Nat}
    (prior : ValidLog op state.rows) (accepted : publish op tasks state order = some next) :
    ValidLog op next.rows := by
  induction order generalizing state with
  | nil => simp only [publish, Option.some.injEq] at accepted; subst next; exact prior
  | cons task rest ih =>
    cases first : complete op tasks state task with
    | none => simp [publish, first] at accepted
    | some middle =>
      simp only [publish, first, Option.bind] at accepted
      exact ih (complete_valid op tasks prior first) accepted

theorem publish_length {Value : Type} (op : Scope → List Value → Value)
    (tasks : List TaskKey) {state next : State Value} {order : List Nat}
    (sameLength : state.origins.length = state.rows.length)
    (accepted : publish op tasks state order = some next) : next.origins.length = next.rows.length := by
  induction order generalizing state with
  | nil => simp only [publish, Option.some.injEq] at accepted; subst next; exact sameLength
  | cons task rest ih =>
    cases first : complete op tasks state task with
    | none => simp [publish, first] at accepted
    | some middle =>
      simp only [publish, first, Option.bind] at accepted
      exact ih (complete_length op tasks sameLength first) accepted

theorem projected_cold_exact {Value : Type} (op : Scope → List Value → Value)
    (tasks : List TaskKey) {next : State Value} {order : List Nat}
    (accepted : publish op tasks empty order = some next) :
    rebuild op [] (next.rows.map Entry.key) = some next.rows :=
  valid_rebuild_exact (publish_valid op tasks .empty accepted)

end Projection
