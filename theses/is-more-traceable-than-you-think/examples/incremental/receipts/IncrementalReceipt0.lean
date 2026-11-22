import Evaluation
namespace IncrementalReceipt0
def history : List Pipeline.Row := []
theorem history_length : history.length = 0 := rfl
theorem certified : Pipeline.check 0 history = true := rfl
theorem semantics (env : Pipeline.Environment) :
    ∃ result, Pipeline.source env [] history = some result ∧
      Pipeline.target env [] history = some result ∧ result.length = history.length :=
  Pipeline.checked_program_correct certified env
end IncrementalReceipt0
#print axioms IncrementalReceipt0.history_length
#print axioms IncrementalReceipt0.certified
#print axioms IncrementalReceipt0.semantics
