import IncrementalReceipt1
namespace IncrementalReceipt2
def history : List Pipeline.Row := IncrementalReceipt1.history
theorem history_length : history.length = 23 := IncrementalReceipt1.history_length
theorem certified : Pipeline.check 0 history = true := IncrementalReceipt1.certified
def value_23 : Evaluation.Tree := .input (String.mk [Char.ofNat 100, Char.ofNat 48]) (3 : Int) [.input (String.mk [Char.ofNat 100, Char.ofNat 48])]
theorem value_23_correct : Evaluation.Correct value_23 (3 : Int) :=
  Evaluation.input_correct  (by decide) (by decide)
def value_24 : Evaluation.Tree := .add IncrementalReceipt2.value_23 IncrementalReceipt2.value_23 [.read 0, .read 1, .add]
theorem value_24_correct : Evaluation.Correct value_24 (6 : Int) :=
  Evaluation.add_correct IncrementalReceipt2.value_23_correct IncrementalReceipt2.value_23_correct (by decide) (by decide)
def value_25 : Evaluation.Tree := .add IncrementalReceipt2.value_24 IncrementalReceipt2.value_24 [.read 0, .read 1, .add]
theorem value_25_correct : Evaluation.Correct value_25 (12 : Int) :=
  Evaluation.add_correct IncrementalReceipt2.value_24_correct IncrementalReceipt2.value_24_correct (by decide) (by decide)
def value_26 : Evaluation.Tree := .add IncrementalReceipt2.value_25 IncrementalReceipt2.value_25 [.read 0, .read 1, .add]
theorem value_26_correct : Evaluation.Correct value_26 (24 : Int) :=
  Evaluation.add_correct IncrementalReceipt2.value_25_correct IncrementalReceipt2.value_25_correct (by decide) (by decide)
def value_27 : Evaluation.Tree := .add IncrementalReceipt2.value_26 IncrementalReceipt2.value_26 [.read 0, .read 1, .add]
theorem value_27_correct : Evaluation.Correct value_27 (48 : Int) :=
  Evaluation.add_correct IncrementalReceipt2.value_26_correct IncrementalReceipt2.value_26_correct (by decide) (by decide)
def value_28 : Evaluation.Tree := .add IncrementalReceipt2.value_27 IncrementalReceipt2.value_27 [.read 0, .read 1, .add]
theorem value_28_correct : Evaluation.Correct value_28 (96 : Int) :=
  Evaluation.add_correct IncrementalReceipt2.value_27_correct IncrementalReceipt2.value_27_correct (by decide) (by decide)
def value_29 : Evaluation.Tree := .add IncrementalReceipt2.value_28 IncrementalReceipt2.value_28 [.read 0, .read 1, .add]
theorem value_29_correct : Evaluation.Correct value_29 (192 : Int) :=
  Evaluation.add_correct IncrementalReceipt2.value_28_correct IncrementalReceipt2.value_28_correct (by decide) (by decide)
def value_30 : Evaluation.Tree := .add IncrementalReceipt2.value_29 IncrementalReceipt2.value_29 [.read 0, .read 1, .add]
theorem value_30_correct : Evaluation.Correct value_30 (384 : Int) :=
  Evaluation.add_correct IncrementalReceipt2.value_29_correct IncrementalReceipt2.value_29_correct (by decide) (by decide)
def value_31 : Evaluation.Tree := .add IncrementalReceipt2.value_30 IncrementalReceipt2.value_30 [.read 0, .read 1, .add]
theorem value_31_correct : Evaluation.Correct value_31 (768 : Int) :=
  Evaluation.add_correct IncrementalReceipt2.value_30_correct IncrementalReceipt2.value_30_correct (by decide) (by decide)
def value_32 : Evaluation.Tree := .add IncrementalReceipt2.value_31 IncrementalReceipt2.value_31 [.read 0, .read 1, .add]
theorem value_32_correct : Evaluation.Correct value_32 (1536 : Int) :=
  Evaluation.add_correct IncrementalReceipt2.value_31_correct IncrementalReceipt2.value_31_correct (by decide) (by decide)
def value_33 : Evaluation.Tree := .add IncrementalReceipt2.value_32 IncrementalReceipt2.value_32 [.read 0, .read 1, .add]
theorem value_33_correct : Evaluation.Correct value_33 (3072 : Int) :=
  Evaluation.add_correct IncrementalReceipt2.value_32_correct IncrementalReceipt2.value_32_correct (by decide) (by decide)
def value_34 : Evaluation.Tree := .add IncrementalReceipt2.value_33 IncrementalReceipt2.value_33 [.read 0, .read 1, .add]
theorem value_34_correct : Evaluation.Correct value_34 (6144 : Int) :=
  Evaluation.add_correct IncrementalReceipt2.value_33_correct IncrementalReceipt2.value_33_correct (by decide) (by decide)
def value_35 : Evaluation.Tree := .add IncrementalReceipt2.value_34 IncrementalReceipt2.value_34 [.read 0, .read 1, .add]
theorem value_35_correct : Evaluation.Correct value_35 (12288 : Int) :=
  Evaluation.add_correct IncrementalReceipt2.value_34_correct IncrementalReceipt2.value_34_correct (by decide) (by decide)
def value_36 : Evaluation.Tree := .add IncrementalReceipt2.value_35 IncrementalReceipt2.value_35 [.read 0, .read 1, .add]
theorem value_36_correct : Evaluation.Correct value_36 (24576 : Int) :=
  Evaluation.add_correct IncrementalReceipt2.value_35_correct IncrementalReceipt2.value_35_correct (by decide) (by decide)
def value_37 : Evaluation.Tree := .add IncrementalReceipt2.value_36 IncrementalReceipt2.value_36 [.read 0, .read 1, .add]
theorem value_37_correct : Evaluation.Correct value_37 (49152 : Int) :=
  Evaluation.add_correct IncrementalReceipt2.value_36_correct IncrementalReceipt2.value_36_correct (by decide) (by decide)
def value_38 : Evaluation.Tree := .add IncrementalReceipt2.value_37 IncrementalReceipt2.value_37 [.read 0, .read 1, .add]
theorem value_38_correct : Evaluation.Correct value_38 (98304 : Int) :=
  Evaluation.add_correct IncrementalReceipt2.value_37_correct IncrementalReceipt2.value_37_correct (by decide) (by decide)
def value_39 : Evaluation.Tree := .add IncrementalReceipt2.value_38 IncrementalReceipt2.value_38 [.read 0, .read 1, .add]
theorem value_39_correct : Evaluation.Correct value_39 (196608 : Int) :=
  Evaluation.add_correct IncrementalReceipt2.value_38_correct IncrementalReceipt2.value_38_correct (by decide) (by decide)
def value_40 : Evaluation.Tree := .add IncrementalReceipt2.value_39 IncrementalReceipt2.value_39 [.read 0, .read 1, .add]
theorem value_40_correct : Evaluation.Correct value_40 (393216 : Int) :=
  Evaluation.add_correct IncrementalReceipt2.value_39_correct IncrementalReceipt2.value_39_correct (by decide) (by decide)
def value_41 : Evaluation.Tree := .add IncrementalReceipt2.value_40 IncrementalReceipt2.value_40 [.read 0, .read 1, .add]
theorem value_41_correct : Evaluation.Correct value_41 (786432 : Int) :=
  Evaluation.add_correct IncrementalReceipt2.value_40_correct IncrementalReceipt2.value_40_correct (by decide) (by decide)
def value_42 : Evaluation.Tree := .add IncrementalReceipt2.value_41 IncrementalReceipt2.value_41 [.read 0, .read 1, .add]
theorem value_42_correct : Evaluation.Correct value_42 (1572864 : Int) :=
  Evaluation.add_correct IncrementalReceipt2.value_41_correct IncrementalReceipt2.value_41_correct (by decide) (by decide)
def value_43 : Evaluation.Tree := .add IncrementalReceipt2.value_42 IncrementalReceipt2.value_42 [.read 0, .read 1, .add]
theorem value_43_correct : Evaluation.Correct value_43 (3145728 : Int) :=
  Evaluation.add_correct IncrementalReceipt2.value_42_correct IncrementalReceipt2.value_42_correct (by decide) (by decide)
theorem semantics (env : Pipeline.Environment) :
    ∃ result, Pipeline.source env [] history = some result ∧
      Pipeline.target env [] history = some result ∧ result.length = history.length :=
  Pipeline.checked_program_correct certified env
end IncrementalReceipt2
#print axioms IncrementalReceipt2.history_length
#print axioms IncrementalReceipt2.certified
#print axioms IncrementalReceipt2.semantics
#print axioms IncrementalReceipt2.value_23_correct
#print axioms IncrementalReceipt2.value_24_correct
#print axioms IncrementalReceipt2.value_25_correct
#print axioms IncrementalReceipt2.value_26_correct
#print axioms IncrementalReceipt2.value_27_correct
#print axioms IncrementalReceipt2.value_28_correct
#print axioms IncrementalReceipt2.value_29_correct
#print axioms IncrementalReceipt2.value_30_correct
#print axioms IncrementalReceipt2.value_31_correct
#print axioms IncrementalReceipt2.value_32_correct
#print axioms IncrementalReceipt2.value_33_correct
#print axioms IncrementalReceipt2.value_34_correct
#print axioms IncrementalReceipt2.value_35_correct
#print axioms IncrementalReceipt2.value_36_correct
#print axioms IncrementalReceipt2.value_37_correct
#print axioms IncrementalReceipt2.value_38_correct
#print axioms IncrementalReceipt2.value_39_correct
#print axioms IncrementalReceipt2.value_40_correct
#print axioms IncrementalReceipt2.value_41_correct
#print axioms IncrementalReceipt2.value_42_correct
#print axioms IncrementalReceipt2.value_43_correct
