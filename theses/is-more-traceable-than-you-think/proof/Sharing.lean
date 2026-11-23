import Incremental

/-!
A shared diamond evaluated by the same append-only kernel. The alternative cost
model literally evaluates both child occurrences recursively. Its calls grow
exponentially while the retained successful invocation count is linear. These
are two specified counts, not a claim about every implementation's running time.
-/
namespace Sharing
open Incremental

def scope (stage : Stage) (index : Nat) : Scope :=
  ⟨stage, 0, 0, 0, 0, 0, 0, [index]⟩

def key (stage : Stage) (index : Nat) : TaskKey :=
  ⟨scope stage index, match index with | 0 => [] | n + 1 => [n, n]⟩

def value {Value : Type} (op : Scope → List Value → Value) (stage : Stage) : Nat → Value
  | 0 => op (scope stage 0) []
  | n + 1 => op (scope stage (n + 1)) [value op stage n, value op stage n]

def row {Value : Type} (op : Scope → List Value → Value) (stage : Stage) (index : Nat) : Entry Value :=
  ⟨key stage index, value op stage index⟩

def cache {Value : Type} (op : Scope → List Value → Value) (stage : Stage) (count : Nat) : Cache Value :=
  (List.range count).map (row op stage)

def requests (stage : Stage) (count : Nat) : List TaskKey :=
  (List.range count).map (key stage)

def unfolded {Value : Type} (op : Scope → List Value → Value) (stage : Stage) : Nat → Value × Nat
  | 0 => (op (scope stage 0) [], 1)
  | n + 1 =>
    let left := unfolded op stage n
    let right := unfolded op stage n
    (op (scope stage (n + 1)) [left.1, right.1], left.2 + right.2 + 1)

theorem cache_succ {Value : Type} (op : Scope → List Value → Value) (stage : Stage) (count : Nat) :
    cache op stage (count + 1) = cache op stage count ++ [row op stage count] := by
  simp only [cache, List.range_succ, List.map_append, List.map_cons, List.map_nil]

theorem cache_length {Value : Type} (op : Scope → List Value → Value) (stage : Stage) (count : Nat) :
    (cache op stage count).length = count := by
  simp only [cache, List.length_map, List.length_range]

theorem cache_row {Value : Type} (op : Scope → List Value → Value) (stage : Stage)
    {index count : Nat} (bound : index < count) :
    (cache op stage count)[index]? = some (row op stage index) := by
  simp only [cache, List.getElem?_map, List.getElem?_range bound, Option.map]

theorem requests_succ (stage : Stage) (count : Nat) :
    requests stage (count + 1) = requests stage count ++ [key stage count] := by
  simp only [requests, List.range_succ, List.map_append, List.map_cons, List.map_nil]

theorem key_fresh {Value : Type} (op : Scope → List Value → Value) (stage : Stage) (count : Nat) :
    lookup (cache op stage count) (key stage count) = none := by
  apply lookup_none.mpr
  intro entry member same
  obtain ⟨index, inRange, entryEq⟩ := List.mem_map.mp member
  subst entry
  have bound := List.mem_range.mp inRange
  have payloadEq := congrArg (fun k : TaskKey => k.scope.payload) same
  have indexEq : index = count := by simpa only [row, key, scope, List.cons.injEq, and_true] using payloadEq
  omega

theorem resolve_children {Value : Type} (op : Scope → List Value → Value) (stage : Stage) (count : Nat) :
    resolve (cache op stage count) (key stage count).premises =
      some (match count with | 0 => [] | n + 1 => [value op stage n, value op stage n]) := by
  cases count with
  | zero => rfl
  | succ n =>
    have found := cache_row op stage (Nat.lt_succ_self n)
    simp only [key, resolve, found, row]

theorem step_succ {Value : Type} (op : Scope → List Value → Value) (stage : Stage) (count : Nat) :
    step op (cache op stage count) (key stage count) = some (cache op stage (count + 1)) := by
  rw [cache_succ]
  simp only [step, key_fresh, resolve_children]
  cases count <;> rfl

theorem run_diamond {Value : Type} (op : Scope → List Value → Value) (stage : Stage) (count : Nat) :
    run op [] (requests stage count) = some (cache op stage count) := by
  induction count with
  | zero => rfl
  | succ n ih =>
    rw [requests_succ, run_append, ih]
    change run op (cache op stage n) [key stage n] = _
    simp only [run, step_succ, Option.bind]

theorem diamond_valid {Value : Type} (op : Scope → List Value → Value) (stage : Stage) (count : Nat) :
    ValidLog op (cache op stage count) := run_valid op .empty (run_diamond op stage count)

theorem work_diamond {Value : Type} (op : Scope → List Value → Value) (stage : Stage) (count : Nat) :
    work (cache op stage count) = count := cache_length op stage count

theorem stageWork_diamond {Value : Type} (op : Scope → List Value → Value) (stage : Stage) (count : Nat) :
    stageWork stage (cache op stage count) = count := by
  induction count with
  | zero => rfl
  | succ n ih =>
    rw [cache_succ, stageWork_append, ih]
    have one : stageWork stage [row op stage n] = 1 := by
      simp [stageWork, row, key, scope]
    rw [one]

theorem unfolded_value {Value : Type} (op : Scope → List Value → Value) (stage : Stage) (depth : Nat) :
    (unfolded op stage depth).1 = value op stage depth := by
  induction depth with
  | zero => rfl
  | succ n ih => simp only [unfolded, value, ih]

theorem unfolded_calls {Value : Type} (op : Scope → List Value → Value) (stage : Stage) (depth : Nat) :
    (unfolded op stage depth).2 = 2 ^ (depth + 1) - 1 := by
  have plusOne : ∀ n, (unfolded op stage n).2 + 1 = 2 ^ (n + 1) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      change (unfolded op stage n).2 + (unfolded op stage n).2 + 1 + 1 = 2 ^ (n + 1 + 1)
      rw [Nat.pow_succ, ← ih]
      omega
  have exactCount := plusOne depth
  omega

theorem diamond_compression {Value : Type} (op : Scope → List Value → Value)
    (stage : Stage) (depth : Nat) :
    run op [] (requests stage (depth + 1)) = some (cache op stage (depth + 1)) ∧
    work (cache op stage (depth + 1)) = depth + 1 ∧
    stageWork stage (cache op stage (depth + 1)) = depth + 1 ∧
    (cache op stage (depth + 1))[depth]? =
      some ⟨key stage depth, (unfolded op stage depth).1⟩ ∧
    (unfolded op stage depth).2 = 2 ^ (depth + 1) - 1 := by
  refine ⟨run_diamond op stage _, work_diamond op stage _, stageWork_diamond op stage _, ?_,
    unfolded_calls op stage depth⟩
  rw [unfolded_value]
  exact cache_row op stage (Nat.lt_succ_self depth)

end Sharing
