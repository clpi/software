import Redundancy

namespace QuotaBoundary
open TestingRedundancy

abbrev Admission := Nat → Bool
def downward (f : Admission) := ∀ lo hi, lo ≤ hi → f hi = true → f lo = true
def threshold (limit n : Nat) := decide (n ≤ limit)
def probes := [127,128]
def agrees (f : Admission) (suite : List Nat) := ∀ n ∈ suite, f n = threshold 127 n

theorem two_determine_all (f : Admission) (shape : downward f) (pass : agrees f probes) :
    ∀ n, f n = threshold 127 n := by
  have below : f 127 = true := pass 127 (by decide)
  have above : f 128 = false := pass 128 (by decide)
  intro n
  by_cases h : n ≤ 127
  · simpa [threshold,h] using shape n 127 h below
  · simp [threshold,h]
    cases hn : f n with
    | false => rfl
    | true =>
      have bad := shape 128 n (by omega) hn
      simp [above] at bad

theorem suite_preserves_acceptance :
    (fun f : Admission => (downward f ∧ agrees f probes) ∧ agrees f (List.range 256)) =
      (fun f => downward f ∧ agrees f probes) :=
  (acceptance_unchanged_iff _ _).mp (fun f ⟨shape, pass⟩ n _ => two_determine_all f shape pass n)

-- Even among pure thresholds these neighbors disagree with the target at just one point.
theorem required_boundaries (suite : List Nat)
    (exactSuite : ∀ limit, agrees (threshold limit) suite → limit = 127) :
    127 ∈ suite ∧ 128 ∈ suite := by
  constructor
  · apply Classical.byContradiction; intro absent
    have eq := exactSuite 126 (by
      intro n hn
      have ne : n ≠ 127 := fun e => absent (e ▸ hn)
      simp [threshold]; omega)
    omega
  · apply Classical.byContradiction; intro absent
    have eq := exactSuite 128 (by
      intro n hn
      have ne : n ≠ 128 := fun e => absent (e ▸ hn)
      simp [threshold]; omega)
    omega

def hole (n : Nat) := threshold 127 n && n != 40
theorem shape_matters : hole 127 = true ∧ hole 128 = false ∧ hole 40 ≠ threshold 127 40 := by decide

#eval ((List.range 256).length, probes)
#print axioms two_determine_all
#print axioms suite_preserves_acceptance
#print axioms required_boundaries
#print axioms shape_matters
end QuotaBoundary
