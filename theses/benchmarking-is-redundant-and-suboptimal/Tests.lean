import Benchmark
namespace BenchmarkTests
open Qualification TestingRedundancy BenchmarkRedundancy

def ctx : Context := ⟨0, 0, 0, 0, 0⟩
def receipt : Receipt := ⟨ctx, 1, 0, 10⟩
def rerun : Receipt := { receipt with sample := 2 }
def stale : Receipt := { receipt with context := { ctx with epoch := 1 } }
def otherVenue : Receipt := { receipt with context := { ctx with venue := 1 } }
def otherProtocol : Receipt := { receipt with context := { ctx with protocol := 1 } }
example : ¬ Derives (fun r => r = receipt) (fun _ _ => False) rerun :=
  fresh_sample_not_derived receipt rerun (by decide)
example : ¬ Derives (fun r => r = receipt) (fun _ _ => False) stale :=
  stale_context_not_derived receipt stale (by decide)
example : ¬ Derives (fun r => r = receipt) (fun _ _ => False) otherVenue :=
  stale_context_not_derived receipt otherVenue (by decide)
example : ¬ Derives (fun r => r = receipt) (fun _ _ => False) otherProtocol :=
  stale_context_not_derived receipt otherProtocol (by decide)
example : Derives (fun r => r = receipt) (fun _ _ => False) receipt := .root rfl

-- Distinct roots jointly satisfy a sample-count obligation. Duplicating the
-- same root does not. This is evidence identity, NOT a statistical IID proof.
def countRules : List Nat → Nat → Prop := fun ps a => ps = [1, 2] ∧ a = 3
example : Derives (fun a => a = 1 ∨ a = 2) countRules 3 := by
  apply Derives.step (ps := [1, 2]) ⟨rfl, rfl⟩
  intro p hp
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
  exact .root hp
example : ¬ Derives (fun a : Nat => a = 1) countRules 3 := by
  intro h
  have hx : (3 : Nat) = 1 := least (X := fun a => a = 1) (fun _ h => h) (by
    intro ps a hr hp
    have bad := hp 2 (by simp [hr.1])
    omega) 3 h
  omega

def fixed : Nat → Prop := fun a => a = 7
def repeated : Plan Nat Bool := ⟨fixed, fun _ => 10⟩
example : Dominates fixed (fun _ _ => False) (skip Bool) repeated := by
  apply covered_positive_plan_dominated
  · intro a ha; exact .root ha
  · exact ⟨true, by decide⟩
example : ¬ Pareto fixed (fun _ _ => False) (fun _ => True) repeated := by
  apply dominated_not_pareto (p := skip Bool) trivial
  apply covered_positive_plan_dominated
  · intro a ha; exact .root ha
  · exact ⟨true, by decide⟩

-- Zero cost is redundant but not strictly dominated by skip.
def zero : Plan Nat Bool := ⟨fixed, fun _ => 0⟩
example : ¬ Dominates fixed (fun _ _ => False) (skip Bool) zero := by
  intro h
  obtain ⟨i, hi⟩ := h.2.2
  exact Nat.not_lt_zero _ hi

-- Coverage/cost tradeoff: greater output does not automatically dominate.
def broad : Plan Nat Bool := ⟨fun _ => True, fun _ => 100⟩
def narrow : Plan Nat Bool := ⟨fun a => a = 7, fun _ => 10⟩
example : ¬ NoWorse broad narrow := by
  intro h
  have bad := h true
  contradiction

-- Functional equivalence does not preserve cost: both return 7, measured
-- declared costs differ. No theorem equates runtime from output identity.
example : broad.cost true ≠ narrow.cost true := by decide

-- A covered outcome does not imply all outcomes of a flaky run are covered.
def outcomes (pass : Bool) : Nat → Prop := fun a => a = if pass then 7 else 8
example : Covered fixed (fun _ _ => False) (outcomes true) := by
  intro a ha; exact .root ha
example : ¬ Covered fixed (fun _ _ => False) (outcomes false) := by
  intro h
  have bad := (no_rules_iff fixed 8).mp (h 8 rfl)
  change (8 : Nat) = 7 at bad
  omega

-- Max aggregation can erase a strict improvement; the additive-context
-- theorem must not be applied to parallel makespan without another proof.
example : (1 : Nat) < 2 ∧ max 1 10 = max 2 10 := by decide

-- Withdrawn origin support cannot keep its old benchmark qualification alive.
example : ¬ Derives (liveRoots fixed fixed) (fun _ _ => False) 7 := by
  intro h
  have bad := (no_rules_iff (liveRoots fixed fixed) 7).mp h
  exact bad.2 bad.1

-- Purpose-relative redundancy can coexist with a new unrelated receipt.
example : PurposeRedundant fixed (fun _ _ => False) (fun a => a = 8) fixed := by
  intro a ha
  constructor
  · intro _; exact .root ha
  · exact monotone (fun _ h => Or.inl h) (fun _ _ h => h) a

end BenchmarkTests
