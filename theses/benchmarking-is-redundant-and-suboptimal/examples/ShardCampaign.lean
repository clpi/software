import Benchmark

namespace ShardCampaign
open BenchmarkRedundancy Qualification

-- An atom is the complete agreed result for one immutable shard in this campaign.
-- Seven are already certified. Shard 3 has new input and requires a fresh result.
abbrev Shard := Fin 8
def ledger (s : Shard) := s ≠ 3
def rules (_ : List Shard) (_ : Shard) : Prop := False
def allShards := List.finRange 8
def fresh := allShards.filter (fun s => decide (s = 3))
def plan (runs : List Shard) : Plan Shard Unit := ⟨fun s => s ∈ runs, fun _ => runs.length⟩

theorem cheaper_covers : Dominates ledger rules (plan fresh) (plan allShards) := by
  refine ⟨?_, ?_, ⟨(), by decide⟩⟩
  · intro a _
    by_cases h : a = 3
    · subst a; exact Derives.root (Or.inr (by change (3 : Shard) ∈ fresh; decide))
    · exact Derives.root (Or.inl h)
  · intro i; cases i; decide

theorem old_off_frontier : ¬ Pareto ledger rules (fun _ => True) (plan allShards) :=
  dominated_not_pareto (hp := True.intro) cheaper_covers

-- A no-call algorithm sees the same seven results in two worlds whose totals differ.
def samples (changed : Nat) := allShards.map (fun s => if s = 3 then changed else 10)
theorem fresh_required : ¬ ∃ report : Nat, ∀ changed, report = (samples changed).sum := by
  rintro ⟨v,h⟩
  exact absurd ((h 10).symm.trans (h 25)) (by decide)

theorem minimum_campaign (xs : List Shard) (complete : Covers ledger rules (plan xs) (plan allShards)) :
    fresh.length ≤ xs.length := by
  have h := complete 3 (by change (3 : Shard) ∈ allShards; decide)
  have root := (no_rules_iff _ _).mp h
  rcases root with h | h
  · exact False.elim (h rfl)
  · change 1 ≤ xs.length
    exact List.length_pos_of_mem h

#eval (allShards.length, fresh.map Fin.val, (samples 10).sum, (samples 25).sum)
#print axioms cheaper_covers
#print axioms old_off_frontier
#print axioms minimum_campaign
#print axioms fresh_required
end ShardCampaign
