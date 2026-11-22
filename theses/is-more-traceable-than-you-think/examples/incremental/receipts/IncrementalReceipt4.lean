import IncrementalReceipt3
namespace IncrementalReceipt4
def delta : List Pipeline.Row := [
  ⟨.input (String.mk [Char.ofNat 100, Char.ofNat 48]), [], [.input (String.mk [Char.ofNat 100, Char.ofNat 48])]⟩,
  ⟨.add, [34, 34], [.read 0, .read 1, .add]⟩,
  ⟨.add, [35, 35], [.read 0, .read 1, .add]⟩,
  ⟨.add, [36, 36], [.read 0, .read 1, .add]⟩,
  ⟨.add, [37, 37], [.read 0, .read 1, .add]⟩,
  ⟨.add, [38, 38], [.read 0, .read 1, .add]⟩,
  ⟨.add, [39, 39], [.read 0, .read 1, .add]⟩,
  ⟨.add, [40, 40], [.read 0, .read 1, .add]⟩,
  ⟨.add, [41, 41], [.read 0, .read 1, .add]⟩,
  ⟨.add, [42, 42], [.read 0, .read 1, .add]⟩,
  ⟨.add, [43, 43], [.read 0, .read 1, .add]⟩,
  ⟨.add, [44, 44], [.read 0, .read 1, .add]⟩,
  ⟨.add, [45, 45], [.read 0, .read 1, .add]⟩,
  ⟨.add, [46, 46], [.read 0, .read 1, .add]⟩,
  ⟨.add, [47, 47], [.read 0, .read 1, .add]⟩,
  ⟨.add, [48, 48], [.read 0, .read 1, .add]⟩,
  ⟨.add, [49, 49], [.read 0, .read 1, .add]⟩,
  ⟨.add, [50, 50], [.read 0, .read 1, .add]⟩,
  ⟨.add, [51, 51], [.read 0, .read 1, .add]⟩,
  ⟨.add, [52, 52], [.read 0, .read 1, .add]⟩,
  ⟨.add, [53, 53], [.read 0, .read 1, .add]⟩,
  ⟨.input (String.mk [Char.ofNat 115, Char.ofNat 105, Char.ofNat 100, Char.ofNat 101]), [], [.input (String.mk [Char.ofNat 115, Char.ofNat 105, Char.ofNat 100, Char.ofNat 101])]⟩,
  ⟨.neg, [55], [.read 0, .neg]⟩
]
theorem delta_checked : Pipeline.check 34 delta = true := by decide
def history : List Pipeline.Row := IncrementalReceipt3.history ++ delta
theorem history_length : history.length = 57 :=
  Pipeline.extension_length IncrementalReceipt3.history_length
    (show delta.length = 23 from by decide)
theorem certified : Pipeline.check 0 history = true :=
  Pipeline.certify_extension IncrementalReceipt3.certified IncrementalReceipt3.history_length delta_checked
def value_55 : Evaluation.Tree := .input (String.mk [Char.ofNat 100, Char.ofNat 48]) (2 : Int) [.input (String.mk [Char.ofNat 100, Char.ofNat 48])]
theorem value_55_correct : Evaluation.Correct value_55 (2 : Int) :=
  Evaluation.input_correct  (by decide) (by decide)
def value_56 : Evaluation.Tree := .add IncrementalReceipt4.value_55 IncrementalReceipt4.value_55 [.read 0, .read 1, .add]
theorem value_56_correct : Evaluation.Correct value_56 (4 : Int) :=
  Evaluation.add_correct IncrementalReceipt4.value_55_correct IncrementalReceipt4.value_55_correct (by decide) (by decide)
def value_57 : Evaluation.Tree := .add IncrementalReceipt4.value_56 IncrementalReceipt4.value_56 [.read 0, .read 1, .add]
theorem value_57_correct : Evaluation.Correct value_57 (8 : Int) :=
  Evaluation.add_correct IncrementalReceipt4.value_56_correct IncrementalReceipt4.value_56_correct (by decide) (by decide)
def value_58 : Evaluation.Tree := .add IncrementalReceipt4.value_57 IncrementalReceipt4.value_57 [.read 0, .read 1, .add]
theorem value_58_correct : Evaluation.Correct value_58 (16 : Int) :=
  Evaluation.add_correct IncrementalReceipt4.value_57_correct IncrementalReceipt4.value_57_correct (by decide) (by decide)
def value_59 : Evaluation.Tree := .add IncrementalReceipt4.value_58 IncrementalReceipt4.value_58 [.read 0, .read 1, .add]
theorem value_59_correct : Evaluation.Correct value_59 (32 : Int) :=
  Evaluation.add_correct IncrementalReceipt4.value_58_correct IncrementalReceipt4.value_58_correct (by decide) (by decide)
def value_60 : Evaluation.Tree := .add IncrementalReceipt4.value_59 IncrementalReceipt4.value_59 [.read 0, .read 1, .add]
theorem value_60_correct : Evaluation.Correct value_60 (64 : Int) :=
  Evaluation.add_correct IncrementalReceipt4.value_59_correct IncrementalReceipt4.value_59_correct (by decide) (by decide)
def value_61 : Evaluation.Tree := .add IncrementalReceipt4.value_60 IncrementalReceipt4.value_60 [.read 0, .read 1, .add]
theorem value_61_correct : Evaluation.Correct value_61 (128 : Int) :=
  Evaluation.add_correct IncrementalReceipt4.value_60_correct IncrementalReceipt4.value_60_correct (by decide) (by decide)
def value_62 : Evaluation.Tree := .add IncrementalReceipt4.value_61 IncrementalReceipt4.value_61 [.read 0, .read 1, .add]
theorem value_62_correct : Evaluation.Correct value_62 (256 : Int) :=
  Evaluation.add_correct IncrementalReceipt4.value_61_correct IncrementalReceipt4.value_61_correct (by decide) (by decide)
def value_63 : Evaluation.Tree := .add IncrementalReceipt4.value_62 IncrementalReceipt4.value_62 [.read 0, .read 1, .add]
theorem value_63_correct : Evaluation.Correct value_63 (512 : Int) :=
  Evaluation.add_correct IncrementalReceipt4.value_62_correct IncrementalReceipt4.value_62_correct (by decide) (by decide)
def value_64 : Evaluation.Tree := .add IncrementalReceipt4.value_63 IncrementalReceipt4.value_63 [.read 0, .read 1, .add]
theorem value_64_correct : Evaluation.Correct value_64 (1024 : Int) :=
  Evaluation.add_correct IncrementalReceipt4.value_63_correct IncrementalReceipt4.value_63_correct (by decide) (by decide)
def value_65 : Evaluation.Tree := .add IncrementalReceipt4.value_64 IncrementalReceipt4.value_64 [.read 0, .read 1, .add]
theorem value_65_correct : Evaluation.Correct value_65 (2048 : Int) :=
  Evaluation.add_correct IncrementalReceipt4.value_64_correct IncrementalReceipt4.value_64_correct (by decide) (by decide)
def value_66 : Evaluation.Tree := .add IncrementalReceipt4.value_65 IncrementalReceipt4.value_65 [.read 0, .read 1, .add]
theorem value_66_correct : Evaluation.Correct value_66 (4096 : Int) :=
  Evaluation.add_correct IncrementalReceipt4.value_65_correct IncrementalReceipt4.value_65_correct (by decide) (by decide)
def value_67 : Evaluation.Tree := .add IncrementalReceipt4.value_66 IncrementalReceipt4.value_66 [.read 0, .read 1, .add]
theorem value_67_correct : Evaluation.Correct value_67 (8192 : Int) :=
  Evaluation.add_correct IncrementalReceipt4.value_66_correct IncrementalReceipt4.value_66_correct (by decide) (by decide)
def value_68 : Evaluation.Tree := .add IncrementalReceipt4.value_67 IncrementalReceipt4.value_67 [.read 0, .read 1, .add]
theorem value_68_correct : Evaluation.Correct value_68 (16384 : Int) :=
  Evaluation.add_correct IncrementalReceipt4.value_67_correct IncrementalReceipt4.value_67_correct (by decide) (by decide)
def value_69 : Evaluation.Tree := .add IncrementalReceipt4.value_68 IncrementalReceipt4.value_68 [.read 0, .read 1, .add]
theorem value_69_correct : Evaluation.Correct value_69 (32768 : Int) :=
  Evaluation.add_correct IncrementalReceipt4.value_68_correct IncrementalReceipt4.value_68_correct (by decide) (by decide)
def value_70 : Evaluation.Tree := .add IncrementalReceipt4.value_69 IncrementalReceipt4.value_69 [.read 0, .read 1, .add]
theorem value_70_correct : Evaluation.Correct value_70 (65536 : Int) :=
  Evaluation.add_correct IncrementalReceipt4.value_69_correct IncrementalReceipt4.value_69_correct (by decide) (by decide)
def value_71 : Evaluation.Tree := .add IncrementalReceipt4.value_70 IncrementalReceipt4.value_70 [.read 0, .read 1, .add]
theorem value_71_correct : Evaluation.Correct value_71 (131072 : Int) :=
  Evaluation.add_correct IncrementalReceipt4.value_70_correct IncrementalReceipt4.value_70_correct (by decide) (by decide)
def value_72 : Evaluation.Tree := .add IncrementalReceipt4.value_71 IncrementalReceipt4.value_71 [.read 0, .read 1, .add]
theorem value_72_correct : Evaluation.Correct value_72 (262144 : Int) :=
  Evaluation.add_correct IncrementalReceipt4.value_71_correct IncrementalReceipt4.value_71_correct (by decide) (by decide)
def value_73 : Evaluation.Tree := .add IncrementalReceipt4.value_72 IncrementalReceipt4.value_72 [.read 0, .read 1, .add]
theorem value_73_correct : Evaluation.Correct value_73 (524288 : Int) :=
  Evaluation.add_correct IncrementalReceipt4.value_72_correct IncrementalReceipt4.value_72_correct (by decide) (by decide)
def value_74 : Evaluation.Tree := .add IncrementalReceipt4.value_73 IncrementalReceipt4.value_73 [.read 0, .read 1, .add]
theorem value_74_correct : Evaluation.Correct value_74 (1048576 : Int) :=
  Evaluation.add_correct IncrementalReceipt4.value_73_correct IncrementalReceipt4.value_73_correct (by decide) (by decide)
def value_75 : Evaluation.Tree := .add IncrementalReceipt4.value_74 IncrementalReceipt4.value_74 [.read 0, .read 1, .add]
theorem value_75_correct : Evaluation.Correct value_75 (2097152 : Int) :=
  Evaluation.add_correct IncrementalReceipt4.value_74_correct IncrementalReceipt4.value_74_correct (by decide) (by decide)
def value_76 : Evaluation.Tree := .input (String.mk [Char.ofNat 115, Char.ofNat 105, Char.ofNat 100, Char.ofNat 101]) (7 : Int) [.input (String.mk [Char.ofNat 115, Char.ofNat 105, Char.ofNat 100, Char.ofNat 101])]
theorem value_76_correct : Evaluation.Correct value_76 (7 : Int) :=
  Evaluation.input_correct  (by decide) (by decide)
def value_77 : Evaluation.Tree := .neg IncrementalReceipt4.value_76 [.read 0, .neg]
theorem value_77_correct : Evaluation.Correct value_77 (-7 : Int) :=
  Evaluation.neg_correct IncrementalReceipt4.value_76_correct (by decide) (by decide)
theorem semantics (env : Pipeline.Environment) :
    ∃ result, Pipeline.source env [] history = some result ∧
      Pipeline.target env [] history = some result ∧ result.length = history.length :=
  Pipeline.checked_program_correct certified env
end IncrementalReceipt4
#print axioms IncrementalReceipt4.history_length
#print axioms IncrementalReceipt4.certified
#print axioms IncrementalReceipt4.semantics
#print axioms IncrementalReceipt4.delta_checked
#print axioms IncrementalReceipt4.value_55_correct
#print axioms IncrementalReceipt4.value_56_correct
#print axioms IncrementalReceipt4.value_57_correct
#print axioms IncrementalReceipt4.value_58_correct
#print axioms IncrementalReceipt4.value_59_correct
#print axioms IncrementalReceipt4.value_60_correct
#print axioms IncrementalReceipt4.value_61_correct
#print axioms IncrementalReceipt4.value_62_correct
#print axioms IncrementalReceipt4.value_63_correct
#print axioms IncrementalReceipt4.value_64_correct
#print axioms IncrementalReceipt4.value_65_correct
#print axioms IncrementalReceipt4.value_66_correct
#print axioms IncrementalReceipt4.value_67_correct
#print axioms IncrementalReceipt4.value_68_correct
#print axioms IncrementalReceipt4.value_69_correct
#print axioms IncrementalReceipt4.value_70_correct
#print axioms IncrementalReceipt4.value_71_correct
#print axioms IncrementalReceipt4.value_72_correct
#print axioms IncrementalReceipt4.value_73_correct
#print axioms IncrementalReceipt4.value_74_correct
#print axioms IncrementalReceipt4.value_75_correct
#print axioms IncrementalReceipt4.value_76_correct
#print axioms IncrementalReceipt4.value_77_correct
