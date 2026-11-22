import IncrementalReceipt0
namespace IncrementalReceipt1
def delta : List Pipeline.Row := [
  ⟨.input (String.mk [Char.ofNat 100, Char.ofNat 48]), [], [.input (String.mk [Char.ofNat 100, Char.ofNat 48])]⟩,
  ⟨.add, [0, 0], [.read 0, .read 1, .add]⟩,
  ⟨.add, [1, 1], [.read 0, .read 1, .add]⟩,
  ⟨.add, [2, 2], [.read 0, .read 1, .add]⟩,
  ⟨.add, [3, 3], [.read 0, .read 1, .add]⟩,
  ⟨.add, [4, 4], [.read 0, .read 1, .add]⟩,
  ⟨.add, [5, 5], [.read 0, .read 1, .add]⟩,
  ⟨.add, [6, 6], [.read 0, .read 1, .add]⟩,
  ⟨.add, [7, 7], [.read 0, .read 1, .add]⟩,
  ⟨.add, [8, 8], [.read 0, .read 1, .add]⟩,
  ⟨.add, [9, 9], [.read 0, .read 1, .add]⟩,
  ⟨.add, [10, 10], [.read 0, .read 1, .add]⟩,
  ⟨.add, [11, 11], [.read 0, .read 1, .add]⟩,
  ⟨.add, [12, 12], [.read 0, .read 1, .add]⟩,
  ⟨.add, [13, 13], [.read 0, .read 1, .add]⟩,
  ⟨.add, [14, 14], [.read 0, .read 1, .add]⟩,
  ⟨.add, [15, 15], [.read 0, .read 1, .add]⟩,
  ⟨.add, [16, 16], [.read 0, .read 1, .add]⟩,
  ⟨.add, [17, 17], [.read 0, .read 1, .add]⟩,
  ⟨.add, [18, 18], [.read 0, .read 1, .add]⟩,
  ⟨.add, [19, 19], [.read 0, .read 1, .add]⟩,
  ⟨.input (String.mk [Char.ofNat 115, Char.ofNat 105, Char.ofNat 100, Char.ofNat 101]), [], [.input (String.mk [Char.ofNat 115, Char.ofNat 105, Char.ofNat 100, Char.ofNat 101])]⟩,
  ⟨.neg, [21], [.read 0, .neg]⟩
]
theorem delta_checked : Pipeline.check 0 delta = true := by decide
def history : List Pipeline.Row := IncrementalReceipt0.history ++ delta
theorem history_length : history.length = 23 :=
  Pipeline.extension_length IncrementalReceipt0.history_length
    (show delta.length = 23 from by decide)
theorem certified : Pipeline.check 0 history = true :=
  Pipeline.certify_extension IncrementalReceipt0.certified IncrementalReceipt0.history_length delta_checked
def value_0 : Evaluation.Tree := .input (String.mk [Char.ofNat 100, Char.ofNat 48]) (2 : Int) [.input (String.mk [Char.ofNat 100, Char.ofNat 48])]
theorem value_0_correct : Evaluation.Correct value_0 (2 : Int) :=
  Evaluation.input_correct  (by decide) (by decide)
def value_1 : Evaluation.Tree := .add IncrementalReceipt1.value_0 IncrementalReceipt1.value_0 [.read 0, .read 1, .add]
theorem value_1_correct : Evaluation.Correct value_1 (4 : Int) :=
  Evaluation.add_correct IncrementalReceipt1.value_0_correct IncrementalReceipt1.value_0_correct (by decide) (by decide)
def value_2 : Evaluation.Tree := .add IncrementalReceipt1.value_1 IncrementalReceipt1.value_1 [.read 0, .read 1, .add]
theorem value_2_correct : Evaluation.Correct value_2 (8 : Int) :=
  Evaluation.add_correct IncrementalReceipt1.value_1_correct IncrementalReceipt1.value_1_correct (by decide) (by decide)
def value_3 : Evaluation.Tree := .add IncrementalReceipt1.value_2 IncrementalReceipt1.value_2 [.read 0, .read 1, .add]
theorem value_3_correct : Evaluation.Correct value_3 (16 : Int) :=
  Evaluation.add_correct IncrementalReceipt1.value_2_correct IncrementalReceipt1.value_2_correct (by decide) (by decide)
def value_4 : Evaluation.Tree := .add IncrementalReceipt1.value_3 IncrementalReceipt1.value_3 [.read 0, .read 1, .add]
theorem value_4_correct : Evaluation.Correct value_4 (32 : Int) :=
  Evaluation.add_correct IncrementalReceipt1.value_3_correct IncrementalReceipt1.value_3_correct (by decide) (by decide)
def value_5 : Evaluation.Tree := .add IncrementalReceipt1.value_4 IncrementalReceipt1.value_4 [.read 0, .read 1, .add]
theorem value_5_correct : Evaluation.Correct value_5 (64 : Int) :=
  Evaluation.add_correct IncrementalReceipt1.value_4_correct IncrementalReceipt1.value_4_correct (by decide) (by decide)
def value_6 : Evaluation.Tree := .add IncrementalReceipt1.value_5 IncrementalReceipt1.value_5 [.read 0, .read 1, .add]
theorem value_6_correct : Evaluation.Correct value_6 (128 : Int) :=
  Evaluation.add_correct IncrementalReceipt1.value_5_correct IncrementalReceipt1.value_5_correct (by decide) (by decide)
def value_7 : Evaluation.Tree := .add IncrementalReceipt1.value_6 IncrementalReceipt1.value_6 [.read 0, .read 1, .add]
theorem value_7_correct : Evaluation.Correct value_7 (256 : Int) :=
  Evaluation.add_correct IncrementalReceipt1.value_6_correct IncrementalReceipt1.value_6_correct (by decide) (by decide)
def value_8 : Evaluation.Tree := .add IncrementalReceipt1.value_7 IncrementalReceipt1.value_7 [.read 0, .read 1, .add]
theorem value_8_correct : Evaluation.Correct value_8 (512 : Int) :=
  Evaluation.add_correct IncrementalReceipt1.value_7_correct IncrementalReceipt1.value_7_correct (by decide) (by decide)
def value_9 : Evaluation.Tree := .add IncrementalReceipt1.value_8 IncrementalReceipt1.value_8 [.read 0, .read 1, .add]
theorem value_9_correct : Evaluation.Correct value_9 (1024 : Int) :=
  Evaluation.add_correct IncrementalReceipt1.value_8_correct IncrementalReceipt1.value_8_correct (by decide) (by decide)
def value_10 : Evaluation.Tree := .add IncrementalReceipt1.value_9 IncrementalReceipt1.value_9 [.read 0, .read 1, .add]
theorem value_10_correct : Evaluation.Correct value_10 (2048 : Int) :=
  Evaluation.add_correct IncrementalReceipt1.value_9_correct IncrementalReceipt1.value_9_correct (by decide) (by decide)
def value_11 : Evaluation.Tree := .add IncrementalReceipt1.value_10 IncrementalReceipt1.value_10 [.read 0, .read 1, .add]
theorem value_11_correct : Evaluation.Correct value_11 (4096 : Int) :=
  Evaluation.add_correct IncrementalReceipt1.value_10_correct IncrementalReceipt1.value_10_correct (by decide) (by decide)
def value_12 : Evaluation.Tree := .add IncrementalReceipt1.value_11 IncrementalReceipt1.value_11 [.read 0, .read 1, .add]
theorem value_12_correct : Evaluation.Correct value_12 (8192 : Int) :=
  Evaluation.add_correct IncrementalReceipt1.value_11_correct IncrementalReceipt1.value_11_correct (by decide) (by decide)
def value_13 : Evaluation.Tree := .add IncrementalReceipt1.value_12 IncrementalReceipt1.value_12 [.read 0, .read 1, .add]
theorem value_13_correct : Evaluation.Correct value_13 (16384 : Int) :=
  Evaluation.add_correct IncrementalReceipt1.value_12_correct IncrementalReceipt1.value_12_correct (by decide) (by decide)
def value_14 : Evaluation.Tree := .add IncrementalReceipt1.value_13 IncrementalReceipt1.value_13 [.read 0, .read 1, .add]
theorem value_14_correct : Evaluation.Correct value_14 (32768 : Int) :=
  Evaluation.add_correct IncrementalReceipt1.value_13_correct IncrementalReceipt1.value_13_correct (by decide) (by decide)
def value_15 : Evaluation.Tree := .add IncrementalReceipt1.value_14 IncrementalReceipt1.value_14 [.read 0, .read 1, .add]
theorem value_15_correct : Evaluation.Correct value_15 (65536 : Int) :=
  Evaluation.add_correct IncrementalReceipt1.value_14_correct IncrementalReceipt1.value_14_correct (by decide) (by decide)
def value_16 : Evaluation.Tree := .add IncrementalReceipt1.value_15 IncrementalReceipt1.value_15 [.read 0, .read 1, .add]
theorem value_16_correct : Evaluation.Correct value_16 (131072 : Int) :=
  Evaluation.add_correct IncrementalReceipt1.value_15_correct IncrementalReceipt1.value_15_correct (by decide) (by decide)
def value_17 : Evaluation.Tree := .add IncrementalReceipt1.value_16 IncrementalReceipt1.value_16 [.read 0, .read 1, .add]
theorem value_17_correct : Evaluation.Correct value_17 (262144 : Int) :=
  Evaluation.add_correct IncrementalReceipt1.value_16_correct IncrementalReceipt1.value_16_correct (by decide) (by decide)
def value_18 : Evaluation.Tree := .add IncrementalReceipt1.value_17 IncrementalReceipt1.value_17 [.read 0, .read 1, .add]
theorem value_18_correct : Evaluation.Correct value_18 (524288 : Int) :=
  Evaluation.add_correct IncrementalReceipt1.value_17_correct IncrementalReceipt1.value_17_correct (by decide) (by decide)
def value_19 : Evaluation.Tree := .add IncrementalReceipt1.value_18 IncrementalReceipt1.value_18 [.read 0, .read 1, .add]
theorem value_19_correct : Evaluation.Correct value_19 (1048576 : Int) :=
  Evaluation.add_correct IncrementalReceipt1.value_18_correct IncrementalReceipt1.value_18_correct (by decide) (by decide)
def value_20 : Evaluation.Tree := .add IncrementalReceipt1.value_19 IncrementalReceipt1.value_19 [.read 0, .read 1, .add]
theorem value_20_correct : Evaluation.Correct value_20 (2097152 : Int) :=
  Evaluation.add_correct IncrementalReceipt1.value_19_correct IncrementalReceipt1.value_19_correct (by decide) (by decide)
def value_21 : Evaluation.Tree := .input (String.mk [Char.ofNat 115, Char.ofNat 105, Char.ofNat 100, Char.ofNat 101]) (7 : Int) [.input (String.mk [Char.ofNat 115, Char.ofNat 105, Char.ofNat 100, Char.ofNat 101])]
theorem value_21_correct : Evaluation.Correct value_21 (7 : Int) :=
  Evaluation.input_correct  (by decide) (by decide)
def value_22 : Evaluation.Tree := .neg IncrementalReceipt1.value_21 [.read 0, .neg]
theorem value_22_correct : Evaluation.Correct value_22 (-7 : Int) :=
  Evaluation.neg_correct IncrementalReceipt1.value_21_correct (by decide) (by decide)
theorem semantics (env : Pipeline.Environment) :
    ∃ result, Pipeline.source env [] history = some result ∧
      Pipeline.target env [] history = some result ∧ result.length = history.length :=
  Pipeline.checked_program_correct certified env
end IncrementalReceipt1
#print axioms IncrementalReceipt1.history_length
#print axioms IncrementalReceipt1.certified
#print axioms IncrementalReceipt1.semantics
#print axioms IncrementalReceipt1.delta_checked
#print axioms IncrementalReceipt1.value_0_correct
#print axioms IncrementalReceipt1.value_1_correct
#print axioms IncrementalReceipt1.value_2_correct
#print axioms IncrementalReceipt1.value_3_correct
#print axioms IncrementalReceipt1.value_4_correct
#print axioms IncrementalReceipt1.value_5_correct
#print axioms IncrementalReceipt1.value_6_correct
#print axioms IncrementalReceipt1.value_7_correct
#print axioms IncrementalReceipt1.value_8_correct
#print axioms IncrementalReceipt1.value_9_correct
#print axioms IncrementalReceipt1.value_10_correct
#print axioms IncrementalReceipt1.value_11_correct
#print axioms IncrementalReceipt1.value_12_correct
#print axioms IncrementalReceipt1.value_13_correct
#print axioms IncrementalReceipt1.value_14_correct
#print axioms IncrementalReceipt1.value_15_correct
#print axioms IncrementalReceipt1.value_16_correct
#print axioms IncrementalReceipt1.value_17_correct
#print axioms IncrementalReceipt1.value_18_correct
#print axioms IncrementalReceipt1.value_19_correct
#print axioms IncrementalReceipt1.value_20_correct
#print axioms IncrementalReceipt1.value_21_correct
#print axioms IncrementalReceipt1.value_22_correct
