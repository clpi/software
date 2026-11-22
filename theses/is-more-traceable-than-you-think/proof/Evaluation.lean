import Pipeline

namespace Evaluation

open Pipeline

inductive Tree where
  | literal (value : Int) (code : List Instruction)
  | input (name : String) (captured : Int) (code : List Instruction)
  | add (left right : Tree) (code : List Instruction)
  | mul (left right : Tree) (code : List Instruction)
  | neg (child : Tree) (code : List Instruction)

/-- Source interpretation of the explicit values captured by this execution. -/
def source : Tree → Int
  | .literal value _ => value
  | .input _ captured _ => captured
  | .add left right _ => source left + source right
  | .mul left right _ => source left * source right
  | .neg child _ => -source child

def zero : Environment := fun _ => 0

def capturedEnvironment (name : String) (value : Int) : Environment :=
  fun queried => if queried = name then value else 0

/-- Target interpretation runs the actual local instructions, using both
    child results for binary blocks. Child trees can be named shared constants. -/
def target : Tree → Option Int
  | .literal _ code => execute zero [] code
  | .input name captured code => execute (capturedEnvironment name captured) [] code
  | .add left right code =>
    (target left).bind fun a => (target right).bind fun b => execute zero [a, b] code
  | .mul left right code =>
    (target left).bind fun a => (target right).bind fun b => execute zero [a, b] code
  | .neg child code => (target child).bind fun a => execute zero [a] code

/-- A checked concrete value, including successful target execution. -/
def Correct (tree : Tree) (result : Int) : Prop :=
  source tree = result ∧ target tree = some result

theorem literal_correct {value result : Int} {code : List Instruction}
    (checked : code = compile (.literal value))
    (computed : value = result) : Correct (.literal value code) result := by
  subst code
  subst result
  exact ⟨rfl, rfl⟩

theorem input_correct {name : String} {captured result : Int}
    {code : List Instruction}
    (checked : code = compile (.input name))
    (computed : captured = result) : Correct (.input name captured code) result := by
  subst code
  subst result
  constructor
  · rfl
  · simp [target, compile_correct, interpret, capturedEnvironment]

theorem add_correct {left right : Tree} {a b result : Int}
    {code : List Instruction}
    (left_correct : Correct left a) (right_correct : Correct right b)
    (checked : code = compile .add) (computed : a + b = result) :
    Correct (.add left right code) result := by
  constructor
  · change source left + source right = result
    rw [left_correct.1, right_correct.1]
    exact computed
  · change (target left).bind (fun x =>
      (target right).bind (fun y => execute zero [x, y] code)) = some result
    rw [left_correct.2, right_correct.2, checked]
    change some (a + b) = some result
    exact congrArg some computed

theorem mul_correct {left right : Tree} {a b result : Int}
    {code : List Instruction}
    (left_correct : Correct left a) (right_correct : Correct right b)
    (checked : code = compile .mul) (computed : a * b = result) :
    Correct (.mul left right code) result := by
  constructor
  · change source left * source right = result
    rw [left_correct.1, right_correct.1]
    exact computed
  · change (target left).bind (fun x =>
      (target right).bind (fun y => execute zero [x, y] code)) = some result
    rw [left_correct.2, right_correct.2, checked]
    change some (a * b) = some result
    exact congrArg some computed

theorem neg_correct {child : Tree} {value result : Int}
    {code : List Instruction}
    (child_correct : Correct child value)
    (checked : code = compile .neg) (computed : -value = result) :
    Correct (.neg child code) result := by
  constructor
  · change -source child = result
    rw [child_correct.1]
    exact computed
  · change (target child).bind (fun x => execute zero [x] code) = some result
    rw [child_correct.2, checked]
    change some (-value) = some result
    exact congrArg some computed

theorem correct_unique_value {tree : Tree} {first second : Int}
    (first_correct : Correct tree first) (second_correct : Correct tree second) :
    first = second := first_correct.1.symm.trans second_correct.1

/-- Consistency with one external input environment is a separate obligation. -/
def Agrees (env : Environment) : Tree → Prop
  | .literal _ _ => True
  | .input name captured _ => env name = captured
  | .add left right _ | .mul left right _ => Agrees env left ∧ Agrees env right
  | .neg child _ => Agrees env child

def globalSource (env : Environment) : Tree → Int
  | .literal value _ => value
  | .input name _ _ => env name
  | .add left right _ => globalSource env left + globalSource env right
  | .mul left right _ => globalSource env left * globalSource env right
  | .neg child _ => -globalSource env child

theorem agrees_source (env : Environment) (tree : Tree)
    (consistent : Agrees env tree) : globalSource env tree = source tree := by
  induction tree with
  | literal value code => rfl
  | input name captured code => exact consistent
  | add left right code ih_left ih_right =>
    change globalSource env left + globalSource env right = source left + source right
    rw [ih_left consistent.1, ih_right consistent.2]
  | mul left right code ih_left ih_right =>
    change globalSource env left * globalSource env right = source left * source right
    rw [ih_left consistent.1, ih_right consistent.2]
  | neg child code ih =>
    change -globalSource env child = -source child
    rw [ih consistent]

theorem agrees_correct {env : Environment} {tree : Tree} {result : Int}
    (consistent : Agrees env tree) (correct : Correct tree result) :
    globalSource env tree = result ∧ target tree = some result :=
  ⟨(agrees_source env tree consistent).trans correct.1, correct.2⟩

#print axioms literal_correct
#print axioms input_correct
#print axioms add_correct
#print axioms mul_correct
#print axioms neg_correct
#print axioms correct_unique_value
#print axioms agrees_source
#print axioms agrees_correct

end Evaluation
