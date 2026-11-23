import Fuzzing
namespace Fuzzing
/-- Finite evidence-plan submission. Authenticity and execution-to-summary adequacy
    are explicit external obligations, not established by these submitted fields. -/
structure FinitePlan (n : Nat) where
  contract : Contract
  covered : Fin n → Bool
  cost : Nat

def FinitePlan.summary (p : FinitePlan n) : Summary (Fin n) :=
  ⟨fun i => p.covered i = true, p.cost⟩

def certify (replacement baseline : FinitePlan n) : Bool :=
  decide (replacement.contract = baseline.contract ∧
    (∀ i, baseline.covered i = true → replacement.covered i = true) ∧
    replacement.cost < baseline.cost)

theorem certify_exact (a b : FinitePlan n) : certify a b = true ↔
    a.contract = b.contract ∧ Dominates a.summary b.summary ∧ a.cost < b.cost := by
  simp only [certify, decide_eq_true_eq]
  constructor
  · rintro ⟨hc, hcov, hcost⟩
    exact ⟨hc, ⟨hcov, Nat.le_of_lt hcost⟩, hcost⟩
  · rintro ⟨hc, hd, hlt⟩
    exact ⟨hc, hd.1, hlt⟩

theorem certified_strict (a b : FinitePlan n) (h : certify a b = true) :
    StrictlyDominates a.summary b.summary := by
  have h' := (certify_exact a b).mp h
  exact ⟨h'.2.1, Or.inl h'.2.2⟩

def base : FinitePlan 2 := ⟨⟨1,1,1,1⟩, fun _ => true, 3⟩
def better : FinitePlan 2 := { base with cost := 2 }
example : certify better base = true := by decide
example : certify base better = false := by decide
example : certify base base = false := by decide
example : certify { better with covered := fun _ => false } base = false := by decide
example : certify { better with contract := ⟨1,2,1,1⟩ } base = false := by decide
#print axioms certify_exact
#print axioms certified_strict
end Fuzzing
