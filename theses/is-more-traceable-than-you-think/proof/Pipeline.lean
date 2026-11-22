import Incremental

namespace Pipeline

inductive Operation where
  | literal (value : Int)
  | input (name : String)
  | add | mul | neg
  deriving DecidableEq, Repr

inductive Instruction where
  | push (value : Int)
  | input (name : String)
  | read (position : Nat)
  | add | mul | neg
  deriving DecidableEq, Repr

abbrev Environment := String → Int

def arity : Operation → Nat
  | .literal _ | .input _ => 0
  | .add | .mul => 2
  | .neg => 1

def interpret (env : Environment) (op : Operation) (args : List Int) : Option Int :=
  match op, args with
  | .literal value, _ => some value
  | .input name, _ => some (env name)
  | .add, a :: b :: _ => some (a + b)
  | .mul, a :: b :: _ => some (a * b)
  | .neg, a :: _ => some (-a)
  | _, _ => none

def compile : Operation → List Instruction
  | .literal value => [.push value]
  | .input name => [.input name]
  | .add => [.read 0, .read 1, .add]
  | .mul => [.read 0, .read 1, .mul]
  | .neg => [.read 0, .neg]

def runStack (env : Environment) (args : List Int) :
    List Instruction → List Int → Option (List Int)
  | [], stack => some stack
  | .push value :: code, stack => runStack env args code (value :: stack)
  | .input name :: code, stack => runStack env args code (env name :: stack)
  | .read position :: code, stack =>
    (args[position]?).bind (fun value => runStack env args code (value :: stack))
  | .add :: code, b :: a :: stack => runStack env args code ((a + b) :: stack)
  | .mul :: code, b :: a :: stack => runStack env args code ((a * b) :: stack)
  | .neg :: code, a :: stack => runStack env args code ((-a) :: stack)
  | _, _ => none

def single : List Int → Option Int
  | [value] => some value
  | _ => none

def execute (env : Environment) (args : List Int) (code : List Instruction) :
    Option Int := (runStack env args code []).bind single

theorem compile_correct (env : Environment) (op : Operation) (args : List Int) :
    execute env args (compile op) = interpret env op args := by
  cases op with
  | literal value => rfl
  | input name => rfl
  | add =>
    cases args with
    | nil => rfl
    | cons a rest => cases rest <;> rfl
  | mul =>
    cases args with
    | nil => rfl
    | cons a rest => cases rest <;> rfl
  | neg => cases args <;> rfl

structure Row where
  operation : Operation
  premises : List Nat
  code : List Instruction
  deriving DecidableEq, Repr

def gather (values : List Int) : List Nat → Option (List Int)
  | [] => some []
  | index :: rest =>
    match values[index]?, gather values rest with
    | some value, some remaining => some (value :: remaining)
    | _, _ => none

theorem gather_resolve (cache : Incremental.Cache Int) (premises : List Nat) :
    gather (cache.map Incremental.Entry.value) premises =
      Incremental.resolve cache premises := by
  induction premises with
  | nil => rfl
  | cons index rest ih =>
    simp only [gather, Incremental.resolve, List.getElem?_map, ih]
    cases cache[index]? <;> cases Incremental.resolve cache rest <;> rfl

def checkRow (available : Nat) (row : Row) : Bool :=
  decide (row.code = compile row.operation) &&
  decide (row.premises.length = arity row.operation) &&
  row.premises.all (fun index => decide (index < available))

def check : Nat → List Row → Bool
  | _, [] => true
  | available, row :: rest => checkRow available row && check (available + 1) rest

theorem checkRow_exact (available : Nat) (row : Row) :
    checkRow available row = true ↔
      row.code = compile row.operation ∧
      row.premises.length = arity row.operation ∧
      ∀ index ∈ row.premises, index < available := by
  simp [checkRow, Bool.and_eq_true, List.all_eq_true, and_assoc]

def sourceStep (env : Environment) (values : List Int) (row : Row) : Option Int :=
  (gather values row.premises).bind (interpret env row.operation)

def targetStep (env : Environment) (values : List Int) (row : Row) : Option Int :=
  (gather values row.premises).bind (fun args => execute env args row.code)

def source (env : Environment) : List Int → List Row → Option (List Int)
  | values, [] => some values
  | values, row :: rest =>
    (sourceStep env values row).bind (fun value => source env (values ++ [value]) rest)

def target (env : Environment) : List Int → List Row → Option (List Int)
  | values, [] => some values
  | values, row :: rest =>
    (targetStep env values row).bind (fun value => target env (values ++ [value]) rest)

theorem checked_row_correct {available : Nat} {row : Row}
    (accepted : checkRow available row = true)
    (env : Environment) (values : List Int) :
    targetStep env values row = sourceStep env values row := by
  have same := ((checkRow_exact available row).mp accepted).1
  simp only [targetStep, sourceStep, same, compile_correct]

theorem checked_semantics {available : Nat} {rows : List Row}
    (accepted : check available rows = true)
    (env : Environment) (values : List Int) :
    target env values rows = source env values rows := by
  induction rows generalizing available values with
  | nil => rfl
  | cons row rest ih =>
    have parts : checkRow available row = true ∧ check (available + 1) rest = true := by
      simpa only [check, Bool.and_eq_true] using accepted
    obtain ⟨head, tail⟩ := parts
    simp only [target, source, checked_row_correct head]
    cases result : sourceStep env values row with
    | none => rfl
    | some value => exact ih tail (values ++ [value])

theorem check_append (available : Nat) (before after : List Row) :
    check available (before ++ after) =
      (check available before && check (available + before.length) after) := by
  induction before generalizing available with
  | nil => simp [check]
  | cons row rest ih =>
    simp only [List.cons_append, check, ih, List.length_cons]
    simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Bool.and_assoc]

theorem certify_extension {before after : List Row} {count : Nat}
    (prior : check 0 before = true) (length : before.length = count)
    (delta : check count after = true) : check 0 (before ++ after) = true := by
  rw [check_append, prior, length, Nat.zero_add, delta]
  rfl

theorem extension_length {before after : List Row} {count extra : Nat}
    (prior : before.length = count) (delta : after.length = extra) :
    (before ++ after).length = count + extra := by
  simp only [List.length_append, prior, delta]

theorem checked_all_prior {available : Nat} {row : Row}
    (accepted : checkRow available row = true) :
    ∀ index ∈ row.premises, index < available := by
  exact ((checkRow_exact available row).mp accepted).2.2

theorem checked_arity {available : Nat} {row : Row}
    (accepted : checkRow available row = true) :
    row.premises.length = arity row.operation := by
  exact ((checkRow_exact available row).mp accepted).2.1

theorem gather_ready (values : List Int) (premises : List Nat)
    (ready : ∀ index ∈ premises, index < values.length) :
    ∃ args, gather values premises = some args ∧ args.length = premises.length := by
  induction premises with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons index rest ih =>
    have bound := ready index (by simp)
    have found : values[index]? = some values[index] :=
      List.getElem?_eq_some_iff.mpr ⟨bound, rfl⟩
    obtain ⟨tail, resolved, length⟩ := ih (fun ref member =>
      ready ref (List.mem_cons_of_mem index member))
    refine ⟨values[index] :: tail, ?_, by simp [length]⟩
    simp only [gather, found, resolved]

theorem interpret_ready (env : Environment) (op : Operation) (args : List Int)
    (length : args.length = arity op) : ∃ value, interpret env op args = some value := by
  cases op with
  | literal value => exact ⟨value, rfl⟩
  | input name => exact ⟨env name, rfl⟩
  | add =>
    cases args with
    | nil => simp [arity] at length
    | cons a rest =>
      cases rest with
      | nil => simp [arity] at length
      | cons b rest => exact ⟨a + b, rfl⟩
  | mul =>
    cases args with
    | nil => simp [arity] at length
    | cons a rest =>
      cases rest with
      | nil => simp [arity] at length
      | cons b rest => exact ⟨a * b, rfl⟩
  | neg =>
    cases args with
    | nil => simp [arity] at length
    | cons a rest => exact ⟨-a, rfl⟩

theorem checked_source_success {available : Nat} {rows : List Row}
    (accepted : check available rows = true) (env : Environment)
    (values : List Int) (length : values.length = available) :
    ∃ result, source env values rows = some result ∧
      result.length = values.length + rows.length := by
  induction rows generalizing available values with
  | nil => exact ⟨values, rfl, by simp⟩
  | cons row rest ih =>
    have parts : checkRow available row = true ∧ check (available + 1) rest = true := by
      simpa only [check, Bool.and_eq_true] using accepted
    obtain ⟨args, resolved, count⟩ := gather_ready values row.premises (by
      simpa only [length] using checked_all_prior parts.1)
    obtain ⟨value, computed⟩ := interpret_ready env row.operation args
      (count.trans (checked_arity parts.1))
    obtain ⟨result, evaluated, size⟩ := ih parts.2 (values ++ [value]) (by simp [length])
    refine ⟨result, ?_, ?_⟩
    · simpa only [source, sourceStep, resolved, computed, Option.bind] using evaluated
    · simpa [List.length_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using size

theorem checked_program_correct {rows : List Row}
    (accepted : check 0 rows = true) (env : Environment) :
    ∃ result, source env [] rows = some result ∧
      target env [] rows = some result ∧ result.length = rows.length := by
  obtain ⟨result, calculated, length⟩ := checked_source_success accepted env [] rfl
  refine ⟨result, calculated, ?_, ?_⟩
  · rw [checked_semantics accepted]
    exact calculated
  · simpa using length

#print axioms compile_correct
#print axioms gather_resolve
#print axioms checkRow_exact
#print axioms checked_row_correct
#print axioms checked_semantics
#print axioms check_append
#print axioms certify_extension
#print axioms extension_length
#print axioms checked_all_prior
#print axioms checked_arity
#print axioms gather_ready
#print axioms interpret_ready
#print axioms checked_source_success
#print axioms checked_program_correct

end Pipeline
