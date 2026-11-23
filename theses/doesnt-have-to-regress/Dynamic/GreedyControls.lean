import Dynamic.Greedy

set_option autoImplicit false

namespace SoftwareDoesntRegress.Dynamic.GreedyControls

open SoftwareDoesntRegress.Audit
open SoftwareDoesntRegress.Dynamic.Greedy
open SoftwareIsQuantifiable.Pareto

def contract : Contract Nat Nat Unit Nat where
  context := 0
  keys := [()]
  prior _ := { qualified := [0] }
  allowed _ := [0]

def release (cost : Point) (offered : List Nat := [0])
    (possible : List Nat := [0]) (context : Nat := 0) :
    ScopedRelease Nat Nat Unit Nat where
  context := context
  profile _ := { offered := { offered := offered }, possible := possible, cost := cost }

/-- Weak publication admits optional capabilities even when the strict cost
    optimizer sees no progress. These are deliberately different operations. -/
theorem weak_publication_is_not_strict_progress :
    let old := release (2, 2)
    let feature := release (2, 2) [0, 1]
    replacement contract old feature = true ∧
      strictImproves contract old feature = false ∧
      (greedyStep contract old feature).profile () = old.profile () := by
  exact ⟨by decide, by decide, rfl⟩

/-- Greedy is deterministic for a supplied order, but incomparable Pareto
    improvements can make the chosen maximal element depend on that order. -/
theorem incomparable_candidates_make_order_matter :
    let old := release (3, 3)
    let a := release (1, 2)
    let b := release (2, 1)
    strictImproves contract old a = true ∧
      strictImproves contract old b = true ∧
      ((greedyFrom contract old [a, b]).profile ()).cost = (1, 2) ∧
      ((greedyFrom contract old [b, a]).profile ()).cost = (2, 1) := by
  decide

/-- A scalar total would prefer this candidate, but its protected first
    coordinate worsens. No scalar score can authorize this transition. -/
theorem aggregate_improvement_does_not_override_protected_cost :
    let old := release (2, 10)
    let candidate := release (3, 0)
    (candidate.profile ()).cost.1 + (candidate.profile ()).cost.2 <
        (old.profile ()).cost.1 + (old.profile ()).cost.2 ∧
      replacement contract old candidate = false ∧
      strictImproves contract old candidate = false := by
  decide

def narrowState : Archive Nat Nat Unit Nat :=
  arrive contract (start (release (2, 2))) [release (1, 1) [0] [0, 1]]

def wider : Contract Nat Nat Unit Nat :=
  { contract with allowed := fun _ => [0, 1] }

/-- Rejected candidates remain in the archive, and a changed envelope can
    make one admissible. A full rescan under the new contract finds it. -/
theorem rejected_candidate_revives_under_changed_contract :
    (narrowState.incumbent.profile ()).cost = (2, 2) ∧
      narrowState.candidates.length = 2 ∧
      strictImproves contract narrowState.incumbent (release (1, 1) [0] [0, 1]) = false ∧
      strictImproves wider narrowState.incumbent (release (1, 1) [0] [0, 1]) = true ∧
      ((reconsider wider narrowState).map fun state =>
        (state.incumbent.profile ()).cost) = some (1, 1) := by
  decide

/-- Reusing the old rejection or scanning only the empty arrival suffix
    after a contract change misses a newly certified improvement. -/
theorem suffix_only_after_contract_change_misses_improvement :
    ((arrive wider narrowState []).incumbent.profile ()).cost = (2, 2) ∧
      strictImproves wider (arrive wider narrowState []).incumbent
        (release (1, 1) [0] [0, 1]) = true := by
  decide

def oneKey : Contract Nat Nat Bool Nat where
  context := 0
  keys := [false]
  prior _ := { qualified := [0] }
  allowed _ := [0]

def twoKeys : Contract Nat Nat Bool Nat :=
  { oneKey with keys := [false, true] }

def keyedRelease (optimized : Bool) : ScopedRelease Nat Nat Bool Nat where
  context := 0
  profile key :=
    { offered := { offered := [0] }, possible := [0]
      cost := if key && !optimized then (2, 2) else (1, 1) }

/-- Revival also occurs during cumulative scope strengthening: previously
    equal candidates can differ on a newly protected key. No promise is erased
    and no old outcome envelope is weakened in this control. -/
theorem newly_protected_key_revives_equal_candidate :
    let state := arrive oneKey (start (keyedRelease false)) [keyedRelease true]
    strictImproves oneKey state.incumbent (keyedRelease true) = false ∧
      certified twoKeys state.incumbent = true ∧
      strictImproves twoKeys state.incumbent (keyedRelease true) = true ∧
      ((reconsider twoKeys state).map fun result =>
        (result.incumbent.profile true).cost) = some (1, 1) := by
  decide

/-- A new promise invalidates the old baseline; even a valid archived
    replacement does not manufacture a no-regression proof from that baseline. -/
theorem changed_qualification_can_invalidate_incumbent :
    let promised := { contract with prior := fun _ => { qualified := [0, 1] } }
    let state := arrive contract (start (release (2, 2))) [release (3, 3) [0, 1]]
    certified contract state.incumbent = true ∧
      certified promised state.incumbent = false ∧
      certified promised (release (3, 3) [0, 1]) = true ∧
      (reconsider promised state).isNone = true := by
  decide

/-- Context labels are rechecked, even if qualification and costs agree. -/
theorem context_change_requires_recertification :
    let changed := { contract with context := 1 }
    certified contract (release (2, 2)) = true ∧
      certified changed (release (2, 2)) = false ∧
      (reconsider changed (start (release (2, 2)))).isNone = true := by
  decide

abbrev Flags := Bool × Bool

def editA (flags : Flags) : Flags := (true, flags.2)
def editB (flags : Flags) : Flags := (flags.1, true)

def flagRelease (flags : Flags) : ScopedRelease Nat Nat Unit Nat :=
  release (if flags.1 && flags.2 then (1, 0)
    else if flags.1 || flags.2 then (3, 0) else (2, 0))

/-- Both edits independently regress. Their combination strictly improves.
    Checking only single edits consequently misses an available combination. -/
theorem singleton_greed_misses_synergy :
    let initial : Flags := (false, false)
    let old := flagRelease initial
    let singletons := [flagRelease (editA initial), flagRelease (editB initial)]
    strictImproves contract old (flagRelease (editA initial)) = false ∧
      strictImproves contract old (flagRelease (editB initial)) = false ∧
      ((greedyFrom contract old singletons).profile ()).cost = (2, 0) ∧
      strictImproves contract old (flagRelease (editA (editB initial))) = true := by
  decide

/-- Enumerating all include/exclude choices in the fixed edit order restores
    the missed combination. Four catalogue entries are actually checked. -/
theorem bounded_bundle_search_recovers_synergy :
    let initial : Flags := (false, false)
    let catalogue := (bundles initial [editA, editB]).map flagRelease
    catalogue.length = 4 ∧
      ((greedyFrom contract (flagRelease initial) catalogue).profile ()).cost = (1, 0) ∧
      (countedSweep contract (flagRelease initial) catalogue).2 = 4 := by
  decide

/-- A candidate generator with reversed edit order can produce a different
    bundle set. The include/exclude theorem does not quantify over permutations. -/
theorem bundle_completeness_is_fixed_order :
    let setOne : Nat → Nat := fun _ => 1
    let increment : Nat → Nat := fun n => n + 1
    (bundles 0 [setOne, increment]) = [0, 1, 1, 1] ∧
      (bundles 0 [increment, setOne]) = [0, 1, 1, 2] := by
  decide

end SoftwareDoesntRegress.Dynamic.GreedyControls
