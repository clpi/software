import Incremental
import Projection

namespace IncrementalControls

open Incremental

def baseScope : Scope := ⟨.evaluation, 0, 0, 0, 0, 0, 0, []⟩
def leaf (value : Nat) : TaskKey := ⟨{baseScope with payload := [value]}, []⟩
def joint (refs : List Nat) : TaskKey := ⟨{baseScope with recipe := 1}, refs⟩
def ordered (refs : List Nat) : TaskKey := ⟨{baseScope with recipe := 2}, refs⟩

def operation (scope : Scope) (inputs : List Nat) : Nat :=
  (if scope.recipe = 0 then scope.payload.sum
   else if scope.recipe = 1 then inputs.sum
   else inputs.foldl (fun total item => 10 * total + item) 0) + scope.source

def initialRows : Cache Nat := [⟨leaf 2, 2⟩]
def seeds : Cache Nat := [⟨leaf 2, 2⟩, ⟨leaf 3, 3⟩]
def composed : Cache Nat := seeds ++ [⟨joint [0, 1], 5⟩]

theorem seed_rows_are_valid : ValidLog operation seeds :=
  run_valid operation [leaf 2, leaf 3] ValidLog.empty (by decide)

/-- One reachable input does not enable an AND derivation requiring two. -/
theorem all_premises_are_required :
    step operation initialRows (joint [0, 1]) = none ∧
    step operation seeds (joint [0, 1]) = some composed := by decide

/-- Neither an empty ledger nor its next row can justify itself. -/
theorem self_support_is_refused :
    step operation [] (joint [0]) = none ∧
    step operation initialRows (joint [1]) = none := by decide

theorem ordered_premises_change_the_result :
    step operation seeds (ordered [0, 1]) =
      some (seeds ++ [⟨ordered [0, 1], 23⟩]) ∧
    step operation seeds (ordered [1, 0]) =
      some (seeds ++ [⟨ordered [1, 0], 32⟩]) := by decide

/-- Repeated argument positions retain multiplicity without republishing a child. -/
theorem repeated_positions_are_not_duplicate_publications :
    step operation initialRows (joint [0, 0]) =
      some (initialRows ++ [⟨joint [0, 0], 4⟩]) ∧
    initialRows.length = 1 := by decide

def changedScopes : List Scope :=
  [{(leaf 2).scope with stage := .compilation},
   {(leaf 2).scope with recipe := 1},
   {(leaf 2).scope with source := 1},
   {(leaf 2).scope with environment := 1},
   {(leaf 2).scope with contract := 1},
   {(leaf 2).scope with toolchain := 1},
   {(leaf 2).scope with checker := 1},
   {(leaf 2).scope with payload := [3]}]

theorem omitted_scope_coordinates_would_alias_distinct_tasks :
    changedScopes.map (fun scope => lookup initialRows ⟨scope, []⟩) =
      List.replicate 8 none := by decide

def nextVersion : TaskKey := ⟨{(leaf 2).scope with source := 1}, []⟩

theorem same_premises_are_not_a_complete_cache_key :
    (leaf 2).premises = nextVersion.premises ∧
    operation (leaf 2).scope [] = 2 ∧
    operation nextVersion.scope [] = 3 ∧
    lookup initialRows nextVersion = none := by decide

def revised : Cache Nat := initialRows ++ [⟨nextVersion, 3⟩]

theorem old_history_survives_a_new_version :
    step operation initialRows nextVersion = some revised ∧
    lookup revised (leaf 2) = some ⟨leaf 2, 2⟩ ∧
    lookup revised nextVersion = some ⟨nextVersion, 3⟩ := by decide

theorem repeated_requests_keep_three_rows :
    run operation [] [leaf 2, leaf 3, joint [0, 1], leaf 2, joint [0, 1], leaf 3] =
      some composed ∧ composed.length = 3 := by decide

def forged : Cache Nat := [⟨leaf 2, 999⟩]

/-- Cache contents are derived by the ledger constructors, not trusted as facts. -/
theorem fabricated_cached_value_is_not_a_valid_log : ¬ ValidLog operation forged := by
  intro valid
  have unequal : rebuild operation [] (forged.map Entry.key) ≠ some forged := by decide
  exact unequal (valid_rebuild_exact operation valid)

def pendingTasks : List TaskKey := [leaf 9, leaf 2, joint [1, 1]]
def projected : Projection.State Nat :=
  ⟨[1, 2], [⟨leaf 2, 2⟩, ⟨joint [0, 0], 4⟩]⟩

theorem sparse_completion_preserves_real_premises :
    Projection.publish operation pendingTasks Projection.empty [1, 2] = some projected ∧
    Projection.remap projected.origins [1, 1] = some [0, 0] := by decide

theorem completion_order_is_not_original_task_order :
    Projection.complete operation pendingTasks projected 0 =
      some ⟨[1, 2, 0], projected.rows ++ [⟨leaf 9, 9⟩]⟩ ∧
    Projection.complete operation pendingTasks projected 2 = none ∧
    Projection.complete operation pendingTasks Projection.empty 2 = none := by decide

end IncrementalControls
