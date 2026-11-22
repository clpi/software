import Std

/-!
An immutable append-only computation log. All premise positions must resolve;
their order and repeated uses are retained. Full scope and prior row references
are the key. The cost below counts successful retained rows, not failed attempts,
storage operations, imports, or wall-clock time.
-/
namespace Incremental

inductive Stage where
  | evaluation | compilation | certification | proving | execution | factoring
  deriving DecidableEq, Repr

structure Scope where
  stage : Stage
  recipe : Nat
  source : Nat
  environment : Nat
  contract : Nat
  toolchain : Nat
  checker : Nat
  payload : List Nat
  deriving DecidableEq, Repr

structure TaskKey where
  scope : Scope
  premises : List Nat
  deriving DecidableEq, Repr

structure Entry (Value : Type) where
  key : TaskKey
  value : Value
  deriving Repr

abbrev Cache (Value : Type) := List (Entry Value)

def resolve {Value : Type} (cache : Cache Value) : List Nat → Option (List Value)
  | [] => some []
  | index :: rest =>
    match cache[index]?, resolve cache rest with
    | some entry, some values => some (entry.value :: values)
    | _, _ => none

def lookup {Value : Type} (cache : Cache Value) (key : TaskKey) : Option (Entry Value) :=
  cache.find? (fun entry => decide (entry.key = key))

def step {Value : Type} (op : Scope → List Value → Value)
    (cache : Cache Value) (key : TaskKey) : Option (Cache Value) :=
  match lookup cache key with
  | some _ => some cache
  | none =>
    match resolve cache key.premises with
    | none => none
    | some values => some (cache ++ [⟨key, op key.scope values⟩])

def run {Value : Type} (op : Scope → List Value → Value)
    (cache : Cache Value) : List TaskKey → Option (Cache Value)
  | [] => some cache
  | key :: rest => (step op cache key).bind (fun next => run op next rest)

def rebuild {Value : Type} (op : Scope → List Value → Value)
    (cache : Cache Value) : List TaskKey → Option (Cache Value)
  | [] => some cache
  | key :: rest => (resolve cache key.premises).bind
      (fun values => rebuild op (cache ++ [⟨key, op key.scope values⟩]) rest)

inductive ValidLog {Value : Type} (op : Scope → List Value → Value) : Cache Value → Prop
  | empty : ValidLog op []
  | append {cache key values} (prior : ValidLog op cache)
      (fresh : lookup cache key = none)
      (ready : resolve cache key.premises = some values) :
      ValidLog op (cache ++ [⟨key, op key.scope values⟩])

def Sound {Value : Type} (op : Scope → List Value → Value) (cache : Cache Value) : Prop :=
  ∀ entry, entry ∈ cache → ∃ values,
    resolve cache entry.key.premises = some values ∧ entry.value = op entry.key.scope values

theorem row_stable {Value : Type} {cache : Cache Value} {index : Nat}
    {entry : Entry Value} (found : cache[index]? = some entry) (more : Cache Value) :
    (cache ++ more)[index]? = some entry := by
  obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp found
  rw [List.getElem?_append_left bound, found]

theorem resolve_append {Value : Type} {cache : Cache Value} {premises : List Nat}
    {values : List Value} (ready : resolve cache premises = some values) (more : Cache Value) :
    resolve (cache ++ more) premises = some values := by
  induction premises generalizing values with
  | nil => exact ready
  | cons index rest ih =>
    cases found : cache[index]? with
    | none => simp [resolve, found] at ready
    | some entry =>
      cases tail : resolve cache rest with
      | none => simp [resolve, found, tail] at ready
      | some vals =>
        simp only [resolve, found, tail, Option.some.injEq] at ready
        subst values
        simp only [resolve, row_stable found more, ih tail]

theorem resolve_all_prior {Value : Type} {cache : Cache Value} {premises : List Nat}
    {values : List Value} (ready : resolve cache premises = some values) :
    ∀ index ∈ premises, index < cache.length := by
  induction premises generalizing values with
  | nil => simp
  | cons first rest ih =>
    cases found : cache[first]? with
    | none => simp [resolve, found] at ready
    | some entry =>
      cases tail : resolve cache rest with
      | none => simp [resolve, found, tail] at ready
      | some vals =>
        intro index member
        rcases List.mem_cons.mp member with same | later
        · subst index
          exact (List.getElem?_eq_some_iff.mp found).1
        · exact ih tail index later

theorem lookup_sound {Value : Type} {cache : Cache Value} {key : TaskKey}
    {entry : Entry Value} (found : lookup cache key = some entry) :
    entry ∈ cache ∧ entry.key = key := by
  have hit : decide (entry.key = key) = true :=
    List.find?_some (p := fun e : Entry Value => decide (e.key = key)) found
  exact ⟨List.mem_of_find?_eq_some found, of_decide_eq_true hit⟩

theorem lookup_none {Value : Type} {cache : Cache Value} {key : TaskKey} :
    lookup cache key = none ↔ ∀ entry ∈ cache, entry.key ≠ key := by
  simp only [lookup, List.find?_eq_none, Bool.not_eq_true, decide_eq_false_iff_not]

theorem step_hit {Value : Type} (op : Scope → List Value → Value)
    {cache : Cache Value} {key : TaskKey} {entry : Entry Value}
    (found : lookup cache key = some entry) : step op cache key = some cache := by
  simp only [step, found]

theorem step_valid {Value : Type} (op : Scope → List Value → Value)
    {cache next : Cache Value} {key : TaskKey} (prior : ValidLog op cache)
    (accepted : step op cache key = some next) : ValidLog op next := by
  cases found : lookup cache key with
  | some entry =>
    simp only [step, found, Option.some.injEq] at accepted
    subst next
    exact prior
  | none =>
    cases ready : resolve cache key.premises with
    | none => simp [step, found, ready] at accepted
    | some values =>
      simp only [step, found, ready, Option.some.injEq] at accepted
      subst next
      exact .append prior found ready

theorem run_valid {Value : Type} (op : Scope → List Value → Value)
    {cache next : Cache Value} {requests : List TaskKey} (prior : ValidLog op cache)
    (accepted : run op cache requests = some next) : ValidLog op next := by
  induction requests generalizing cache with
  | nil =>
    simp only [run, Option.some.injEq] at accepted
    subst next
    exact prior
  | cons key rest ih =>
    cases first : step op cache key with
    | none => simp [run, first] at accepted
    | some middle =>
      simp only [run, first, Option.bind_some] at accepted
      exact ih (step_valid op prior first) accepted

theorem valid_sound {Value : Type} {op : Scope → List Value → Value}
    {cache : Cache Value} (valid : ValidLog op cache) : Sound op cache := by
  induction valid with
  | empty => intro entry member; cases member
  | @append cache key values prior fresh ready ih =>
    intro entry member
    rcases List.mem_append.mp member with old | new
    · obtain ⟨inputs, resolved, correct⟩ := ih entry old
      exact ⟨inputs, resolve_append resolved _, correct⟩
    · have same := List.mem_singleton.mp new
      subst entry
      exact ⟨values, resolve_append ready _, rfl⟩

theorem reuse_agrees_with_fresh {Value : Type} (op : Scope → List Value → Value)
    {cache : Cache Value} {key : TaskKey} {entry : Entry Value}
    (valid : ValidLog op cache) (found : lookup cache key = some entry) :
    ∃ values, resolve cache key.premises = some values ∧
      entry.value = op key.scope values ∧ step op cache key = some cache := by
  obtain ⟨member, same⟩ := lookup_sound found
  obtain ⟨values, ready, correct⟩ := valid_sound valid entry member
  exact ⟨values, same ▸ ready, same ▸ correct, step_hit op found⟩

theorem run_append {Value : Type} (op : Scope → List Value → Value)
    (cache : Cache Value) (left right : List TaskKey) :
    run op cache (left ++ right) = (run op cache left).bind (fun next => run op next right) := by
  induction left generalizing cache with
  | nil => rfl
  | cons key rest ih =>
    simp only [List.cons_append, run]
    cases step op cache key with
    | none => rfl
    | some next => exact ih next

theorem rebuild_append {Value : Type} (op : Scope → List Value → Value)
    (cache : Cache Value) (left right : List TaskKey) :
    rebuild op cache (left ++ right) =
      (rebuild op cache left).bind (fun next => rebuild op next right) := by
  induction left generalizing cache with
  | nil => rfl
  | cons key rest ih =>
    simp only [List.cons_append, rebuild]
    cases resolve cache key.premises with
    | none => rfl
    | some values => exact ih _

theorem valid_rebuild_exact {Value : Type} {op : Scope → List Value → Value}
    {cache : Cache Value} (valid : ValidLog op cache) :
    rebuild op [] (cache.map Entry.key) = some cache := by
  induction valid with
  | empty => rfl
  | @append cache key values prior fresh ready ih =>
    simp only [List.map_append, List.map_cons, List.map_nil,
      rebuild_append, ih, Option.bind_some, rebuild, ready]
    change (resolve cache key.premises).bind
      (fun inputs => some (cache ++ [⟨key, op key.scope inputs⟩])) = _
    rw [ready]
    rfl

theorem run_cold_exact {Value : Type} (op : Scope → List Value → Value)
    {requests : List TaskKey} {cache : Cache Value}
    (accepted : run op [] requests = some cache) :
    rebuild op [] (cache.map Entry.key) = some cache :=
  valid_rebuild_exact (run_valid op .empty accepted)

theorem step_preserves_prefix {Value : Type} (op : Scope → List Value → Value)
    {cache next : Cache Value} {key : TaskKey} (accepted : step op cache key = some next) :
    ∃ more, next = cache ++ more := by
  cases found : lookup cache key with
  | some entry =>
    simp only [step, found, Option.some.injEq] at accepted
    exact ⟨[], by simpa only [List.append_nil] using accepted.symm⟩
  | none =>
    cases ready : resolve cache key.premises with
    | none => simp [step, found, ready] at accepted
    | some values =>
      simp only [step, found, ready, Option.some.injEq] at accepted
      exact ⟨[⟨key, op key.scope values⟩], accepted.symm⟩

theorem run_preserves_prefix {Value : Type} (op : Scope → List Value → Value)
    {cache next : Cache Value} {requests : List TaskKey}
    (accepted : run op cache requests = some next) : ∃ more, next = cache ++ more := by
  induction requests generalizing cache with
  | nil =>
    simp only [run, Option.some.injEq] at accepted
    exact ⟨[], by simpa only [List.append_nil] using accepted.symm⟩
  | cons key rest ih =>
    cases first : step op cache key with
    | none => simp [run, first] at accepted
    | some middle =>
      simp only [run, first, Option.bind_some] at accepted
      obtain ⟨a, ha⟩ := step_preserves_prefix op first
      obtain ⟨b, hb⟩ := ih accepted
      exact ⟨a ++ b, by rw [hb, ha, List.append_assoc]⟩

theorem valid_unique_keys {Value : Type} {op : Scope → List Value → Value}
    {cache : Cache Value} (valid : ValidLog op cache) : (cache.map Entry.key).Nodup := by
  induction valid with
  | empty => exact List.Pairwise.nil
  | @append cache key values prior fresh ready ih =>
    rw [List.map_append]
    apply List.pairwise_append.mpr
    refine ⟨ih, by simp, ?_⟩
    intro old oldMember new newMember
    obtain ⟨entry, member, same⟩ := List.mem_map.mp oldMember
    have newEq : new = key := by simpa using newMember
    subst old
    subst new
    exact lookup_none.mp fresh entry member

def work {Value : Type} (cache : Cache Value) : Nat := cache.length

def stageWork {Value : Type} (stage : Stage) (cache : Cache Value) : Nat :=
  (cache.filter (fun entry => decide (entry.key.scope.stage = stage))).length

theorem work_append {Value : Type} (cache more : Cache Value) :
    work (cache ++ more) = work cache + work more := List.length_append

theorem stageWork_append {Value : Type} (stage : Stage) (cache more : Cache Value) :
    stageWork stage (cache ++ more) = stageWork stage cache + stageWork stage more := by
  simp only [stageWork, List.filter_append, List.length_append]

theorem cumulative_work {Value : Type} (op : Scope → List Value → Value)
    {cache next : Cache Value} {requests : List TaskKey}
    (accepted : run op cache requests = some next) :
    ∃ more, next = cache ++ more ∧ work next = work cache + work more ∧
      ∀ stage, stageWork stage next = stageWork stage cache + stageWork stage more := by
  obtain ⟨more, same⟩ := run_preserves_prefix op accepted
  exact ⟨more, same, same ▸ work_append cache more,
    fun stage => same ▸ stageWork_append stage cache more⟩

theorem hit_zero_work {Value : Type} (op : Scope → List Value → Value)
    {cache : Cache Value} {key : TaskKey} {entry : Entry Value}
    (found : lookup cache key = some entry) :
    step op cache key = some cache ∧ work cache - work cache = 0 :=
  ⟨step_hit op found, Nat.sub_self _⟩

theorem miss_one_work {Value : Type} (op : Scope → List Value → Value)
    {cache : Cache Value} {key : TaskKey} {values : List Value}
    (fresh : lookup cache key = none) (ready : resolve cache key.premises = some values) :
    step op cache key = some (cache ++ [⟨key, op key.scope values⟩]) ∧
      work (cache ++ [⟨key, op key.scope values⟩]) = work cache + 1 := by
  constructor
  · simp only [step, fresh, ready]
  · simp only [work, List.length_append, List.length_singleton]

theorem resolve_member {Value : Type} {cache : Cache Value} {premises : List Nat}
    {values : List Value} (ready : resolve cache premises = some values)
    {value : Value} (member : value ∈ values) :
    ∃ index ∈ premises, ∃ entry, cache[index]? = some entry ∧ entry.value = value := by
  induction premises generalizing values with
  | nil => simp [resolve] at ready; subst values; cases member
  | cons index rest ih =>
    cases found : cache[index]? with
    | none => simp [resolve, found] at ready
    | some entry =>
      cases tail : resolve cache rest with
      | none => simp [resolve, found, tail] at ready
      | some vals =>
        simp only [resolve, found, tail, Option.some.injEq] at ready
        subst values
        rcases List.mem_cons.mp member with same | later
        · exact ⟨index, List.mem_cons_self, entry, found, same.symm⟩
        · obtain ⟨i, him, e, he, hv⟩ := ih tail later
          exact ⟨i, List.mem_cons_of_mem _ him, e, he, hv⟩

theorem resolve_length {Value : Type} {cache : Cache Value} {premises : List Nat}
    {values : List Value} (ready : resolve cache premises = some values) :
    values.length = premises.length := by
  induction premises generalizing values with
  | nil => simp [resolve] at ready; subst values; rfl
  | cons index rest ih =>
    cases found : cache[index]? with
    | none => simp [resolve, found] at ready
    | some entry =>
      cases tail : resolve cache rest with
      | none => simp [resolve, found, tail] at ready
      | some vals =>
        simp only [resolve, found, tail, Option.some.injEq] at ready
        subst values
        simp only [List.length_cons, ih tail]

theorem cumulative_contract {Value : Type} {op : Scope → List Value → Value}
    {P : Value → Prop} (localSound : ∀ scope values,
      (∀ value ∈ values, P value) → P (op scope values))
    {cache : Cache Value} (valid : ValidLog op cache) : ∀ entry ∈ cache, P entry.value := by
  induction valid with
  | empty => intro entry member; cases member
  | @append cache key values prior fresh ready ih =>
    intro entry member
    rcases List.mem_append.mp member with old | new
    · exact ih entry old
    · have same := List.mem_singleton.mp new
      subst entry
      apply localSound
      intro value member
      obtain ⟨index, _, row, found, correct⟩ := resolve_member ready member
      rw [← correct]
      exact ih row (List.mem_of_getElem? found)

theorem valid_backward {Value : Type} {op : Scope → List Value → Value}
    {cache : Cache Value} (valid : ValidLog op cache) {index : Nat} {entry : Entry Value}
    (found : cache[index]? = some entry) : ∀ premise ∈ entry.key.premises, premise < index := by
  induction valid with
  | empty => simp at found
  | @append cache key values prior fresh ready ih =>
    by_cases old : index < cache.length
    · rw [List.getElem?_append_left old] at found
      exact ih found
    · have limit := (List.getElem?_eq_some_iff.mp found).1
      have indexEq : index = cache.length := by simp only [List.length_append, List.length_singleton] at limit; omega
      subst index
      have entryEq : entry = ⟨key, op key.scope values⟩ := by
        simpa only [List.getElem?_concat_length, Option.some.injEq] using found.symm
      subst entry
      exact resolve_all_prior ready

inductive Depends {Value : Type} (cache : Cache Value) : Nat → Nat → Prop
  | direct {parent child : Nat} {entry : Entry Value}
      (found : cache[parent]? = some entry) (member : child ∈ entry.key.premises) :
      Depends cache parent child
  | trans {parent middle child : Nat} (first : Depends cache parent middle)
      (rest : Depends cache middle child) : Depends cache parent child

theorem dependency_rank {Value : Type} {op : Scope → List Value → Value}
    {cache : Cache Value} (valid : ValidLog op cache) {parent child : Nat}
    (path : Depends cache parent child) : child < parent := by
  induction path with
  | direct found member => exact valid_backward valid found _ member
  | trans first rest ih₁ ih₂ => exact Nat.lt_trans ih₂ ih₁

theorem no_self_support {Value : Type} {op : Scope → List Value → Value}
    {cache : Cache Value} (valid : ValidLog op cache) (index : Nat) : ¬ Depends cache index index := by
  intro path
  exact Nat.lt_irrefl index (dependency_rank valid path)

def keyWork {Value : Type} (key : TaskKey) (cache : Cache Value) : Nat :=
  (cache.filter (fun entry => decide (entry.key = key))).length

theorem keyWork_append {Value : Type} (key : TaskKey) (cache more : Cache Value) :
    keyWork key (cache ++ more) = keyWork key cache + keyWork key more := by
  simp only [keyWork, List.filter_append, List.length_append]

theorem keyWork_singleton {Value : Type} (key : TaskKey) (entry : Entry Value) :
    keyWork key [entry] = if entry.key = key then 1 else 0 := by
  by_cases same : entry.key = key
  · simp only [keyWork, List.filter_cons, same, decide_true, Bool.true_eq, if_true,
      List.filter_nil, List.length_singleton]
  · simp only [keyWork, List.filter_cons, same, decide_false, Bool.false_eq_true, if_false,
      List.filter_nil, List.length_nil]

theorem fresh_key_zero_work {Value : Type} {key : TaskKey} {cache : Cache Value}
    (fresh : lookup cache key = none) : keyWork key cache = 0 := by
  have absent := lookup_none.mp fresh
  unfold keyWork
  have empty : cache.filter (fun entry => decide (entry.key = key)) = [] := by
    induction cache with
    | nil => rfl
    | cons entry rest ih =>
      have noHead := absent entry List.mem_cons_self
      have noTail : ∀ e ∈ rest, e.key ≠ key := fun e member => absent e (List.mem_cons_of_mem _ member)
      simp only [List.filter_cons, noHead, decide_false, Bool.false_eq_true, if_false,
        ih (lookup_none.mpr noTail) noTail]
  rw [empty]
  rfl

theorem key_work_at_most_one {Value : Type} {op : Scope → List Value → Value}
    {cache : Cache Value} (valid : ValidLog op cache) (key : TaskKey) : keyWork key cache ≤ 1 := by
  induction valid with
  | empty => exact Nat.zero_le _
  | @append cache newKey values prior fresh ready ih =>
    rw [keyWork_append, keyWork_singleton]
    by_cases same : newKey = key
    · subst newKey
      rw [if_pos rfl, fresh_key_zero_work fresh]
      exact Nat.le_refl _
    · rw [if_neg same, Nat.add_zero]
      exact ih

end Incremental
