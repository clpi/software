import IncrementalReceipt2
namespace IncrementalReceipt3
def delta : List Pipeline.Row := [
  ⟨.neg, [9], [.read 0, .neg]⟩,
  ⟨.add, [23, 23], [.read 0, .read 1, .add]⟩,
  ⟨.add, [24, 24], [.read 0, .read 1, .add]⟩,
  ⟨.add, [25, 25], [.read 0, .read 1, .add]⟩,
  ⟨.add, [26, 26], [.read 0, .read 1, .add]⟩,
  ⟨.add, [27, 27], [.read 0, .read 1, .add]⟩,
  ⟨.add, [28, 28], [.read 0, .read 1, .add]⟩,
  ⟨.add, [29, 29], [.read 0, .read 1, .add]⟩,
  ⟨.add, [30, 30], [.read 0, .read 1, .add]⟩,
  ⟨.add, [31, 31], [.read 0, .read 1, .add]⟩,
  ⟨.add, [32, 32], [.read 0, .read 1, .add]⟩
]
theorem delta_checked : Pipeline.check 23 delta = true := by decide
def history : List Pipeline.Row := IncrementalReceipt2.history ++ delta
theorem history_length : history.length = 34 :=
  Pipeline.extension_length IncrementalReceipt2.history_length
    (show delta.length = 11 from by decide)
theorem certified : Pipeline.check 0 history = true :=
  Pipeline.certify_extension IncrementalReceipt2.certified IncrementalReceipt2.history_length delta_checked
def value_44 : Evaluation.Tree := .neg IncrementalReceipt2.value_32 [.read 0, .neg]
theorem value_44_correct : Evaluation.Correct value_44 (-1536 : Int) :=
  Evaluation.neg_correct IncrementalReceipt2.value_32_correct (by decide) (by decide)
def value_45 : Evaluation.Tree := .add IncrementalReceipt3.value_44 IncrementalReceipt3.value_44 [.read 0, .read 1, .add]
theorem value_45_correct : Evaluation.Correct value_45 (-3072 : Int) :=
  Evaluation.add_correct IncrementalReceipt3.value_44_correct IncrementalReceipt3.value_44_correct (by decide) (by decide)
def value_46 : Evaluation.Tree := .add IncrementalReceipt3.value_45 IncrementalReceipt3.value_45 [.read 0, .read 1, .add]
theorem value_46_correct : Evaluation.Correct value_46 (-6144 : Int) :=
  Evaluation.add_correct IncrementalReceipt3.value_45_correct IncrementalReceipt3.value_45_correct (by decide) (by decide)
def value_47 : Evaluation.Tree := .add IncrementalReceipt3.value_46 IncrementalReceipt3.value_46 [.read 0, .read 1, .add]
theorem value_47_correct : Evaluation.Correct value_47 (-12288 : Int) :=
  Evaluation.add_correct IncrementalReceipt3.value_46_correct IncrementalReceipt3.value_46_correct (by decide) (by decide)
def value_48 : Evaluation.Tree := .add IncrementalReceipt3.value_47 IncrementalReceipt3.value_47 [.read 0, .read 1, .add]
theorem value_48_correct : Evaluation.Correct value_48 (-24576 : Int) :=
  Evaluation.add_correct IncrementalReceipt3.value_47_correct IncrementalReceipt3.value_47_correct (by decide) (by decide)
def value_49 : Evaluation.Tree := .add IncrementalReceipt3.value_48 IncrementalReceipt3.value_48 [.read 0, .read 1, .add]
theorem value_49_correct : Evaluation.Correct value_49 (-49152 : Int) :=
  Evaluation.add_correct IncrementalReceipt3.value_48_correct IncrementalReceipt3.value_48_correct (by decide) (by decide)
def value_50 : Evaluation.Tree := .add IncrementalReceipt3.value_49 IncrementalReceipt3.value_49 [.read 0, .read 1, .add]
theorem value_50_correct : Evaluation.Correct value_50 (-98304 : Int) :=
  Evaluation.add_correct IncrementalReceipt3.value_49_correct IncrementalReceipt3.value_49_correct (by decide) (by decide)
def value_51 : Evaluation.Tree := .add IncrementalReceipt3.value_50 IncrementalReceipt3.value_50 [.read 0, .read 1, .add]
theorem value_51_correct : Evaluation.Correct value_51 (-196608 : Int) :=
  Evaluation.add_correct IncrementalReceipt3.value_50_correct IncrementalReceipt3.value_50_correct (by decide) (by decide)
def value_52 : Evaluation.Tree := .add IncrementalReceipt3.value_51 IncrementalReceipt3.value_51 [.read 0, .read 1, .add]
theorem value_52_correct : Evaluation.Correct value_52 (-393216 : Int) :=
  Evaluation.add_correct IncrementalReceipt3.value_51_correct IncrementalReceipt3.value_51_correct (by decide) (by decide)
def value_53 : Evaluation.Tree := .add IncrementalReceipt3.value_52 IncrementalReceipt3.value_52 [.read 0, .read 1, .add]
theorem value_53_correct : Evaluation.Correct value_53 (-786432 : Int) :=
  Evaluation.add_correct IncrementalReceipt3.value_52_correct IncrementalReceipt3.value_52_correct (by decide) (by decide)
def value_54 : Evaluation.Tree := .add IncrementalReceipt3.value_53 IncrementalReceipt3.value_53 [.read 0, .read 1, .add]
theorem value_54_correct : Evaluation.Correct value_54 (-1572864 : Int) :=
  Evaluation.add_correct IncrementalReceipt3.value_53_correct IncrementalReceipt3.value_53_correct (by decide) (by decide)
theorem semantics (env : Pipeline.Environment) :
    ∃ result, Pipeline.source env [] history = some result ∧
      Pipeline.target env [] history = some result ∧ result.length = history.length :=
  Pipeline.checked_program_correct certified env
end IncrementalReceipt3
#print axioms IncrementalReceipt3.history_length
#print axioms IncrementalReceipt3.certified
#print axioms IncrementalReceipt3.semantics
#print axioms IncrementalReceipt3.delta_checked
#print axioms IncrementalReceipt3.value_44_correct
#print axioms IncrementalReceipt3.value_45_correct
#print axioms IncrementalReceipt3.value_46_correct
#print axioms IncrementalReceipt3.value_47_correct
#print axioms IncrementalReceipt3.value_48_correct
#print axioms IncrementalReceipt3.value_49_correct
#print axioms IncrementalReceipt3.value_50_correct
#print axioms IncrementalReceipt3.value_51_correct
#print axioms IncrementalReceipt3.value_52_correct
#print axioms IncrementalReceipt3.value_53_correct
#print axioms IncrementalReceipt3.value_54_correct
