import Evaluation

namespace EvaluationControls

open Evaluation

/-- Both leaf records name the same input, but record different invocations. -/
def capturedOne : Tree := .input "x" 1 (Pipeline.compile (.input "x"))
def capturedTwo : Tree := .input "x" 2 (Pipeline.compile (.input "x"))
def conflictingCaptures : Tree :=
  .add capturedOne capturedTwo (Pipeline.compile .add)

/-- Exact weaker claim: the captured source and actual target both return 3. -/
theorem conflicting_captures_have_captured_correctness :
    Correct conflictingCaptures 3 := by
  exact add_correct
    (show Correct capturedOne 1 from input_correct rfl rfl)
    (show Correct capturedTwo 2 from input_correct rfl rfl) rfl rfl

/-- Captured correctness cannot establish one consistent external environment. -/
theorem conflicting_captures_have_no_global_environment :
    ∀ env : Pipeline.Environment, ¬ Agrees env conflictingCaptures := by
  intro env consistent
  change env "x" = 1 ∧ env "x" = 2 at consistent
  exact (by decide : (1 : Int) ≠ 2) (consistent.1.symm.trans consistent.2)

/-- Even the weaker captured statement refuses a fabricated concrete result. -/
theorem fabricated_captured_value_is_refused :
    ¬ Correct conflictingCaptures 999 := by
  intro forged
  exact (by decide : (3 : Int) ≠ 999)
    (correct_unique_value conflicting_captures_have_captured_correctness forged)

#print axioms conflicting_captures_have_captured_correctness
#print axioms conflicting_captures_have_no_global_environment
#print axioms fabricated_captured_value_is_refused

end EvaluationControls
