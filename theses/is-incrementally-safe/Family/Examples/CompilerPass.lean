import Family.Dataflow

/-!
# Worked example 1: a compiler pass

Five components: `lex`, `parse`, `fold` (constant folding), `emit` (code generation), and
`docs` (a documentation generator that counts literals). Each component's code is a stage
`List Nat → List Nat`; its behavior is its stage composed after its dependency's behavior.
Programs are lists of literals whose meaning is their sum.

Properties (the spec, trusted): parsing and folding keep the meaning; `emit` computes exactly
what a reference interpreter computes (semantic preservation); `docs` reports the literal count.

* `good_change_admitted`: the parser is changed to reverse its output. Rechecking the cone
  (`parse`, `fold`, `emit`, `docs`) is enough to admit the whole release; `lex` is not re-run.
* `bad_change`: the parser is changed to drop zero literals. The changed component passes its
  own check (meaning is kept), so a changed-only check admits it, but `docs`, a dependent, now
  reports the wrong count. The cone check refuses it.

Premises: `Local` is not assumed, it is `dataflow_local` (each stage reads only its declared
dependency). The spec `Q` is trusted.
-/
namespace Family.Examples.CompilerPass

open Family.Dataflow Family.Selection SoftwareIsIncrementallySafe.OrderedIncrement

inductive Sym where
  | lex | parse | fold | emit | docs
  deriving DecidableEq, Repr

def parent : Sym → Option Sym
  | .lex => none
  | .parse => some .lex
  | .fold => some .parse
  | .emit => some .fold
  | .docs => some .parse

def dep (s t : Sym) : Bool := parent s == some t

abbrev Stage := List Nat → List Nat

def step (s : Sym) (c : Stage) (f : Sym → Stage) : Stage :=
  match parent s with
  | none => c
  | some p => fun xs => c (f p xs)

def sem (I : Sym → Stage) (s : Sym) : Stage := run dep step id I 4 s

def Q : Sym → Stage → Prop
  | .lex, b => ∀ xs, (b xs).sum = xs.sum
  | .parse, b => ∀ xs, (b xs).sum = xs.sum
  | .fold, b => ∀ xs, (b xs).sum = xs.sum
  | .emit, b => ∀ xs, b xs = [xs.sum]
  | .docs, b => ∀ xs, b xs = [xs.length]

def old : Sym → Stage
  | .lex => id
  | .parse => id
  | .fold => fun xs => [xs.sum]
  | .emit => id
  | .docs => fun xs => [xs.length]

theorem sum_app : ∀ a b : List Nat, (a ++ b).sum = a.sum + b.sum
  | [], b => by simp
  | x :: a, b => by simp [sum_app a b]; omega

theorem sum_rev : ∀ xs : List Nat, xs.reverse.sum = xs.sum
  | [] => rfl
  | x :: xs => by simp [sum_app, sum_rev xs]; omega

theorem sem_local : Local (Deps dep) sem := dataflow_local dep step id 4

theorem old_good : ∀ s, Q s (sem old s) := by
  intro s; cases s <;> intro xs <;> simp [Q, sem, run, step, parent, dep, old]

def onlyParse : Sym → Bool := fun s => s == .parse

/-- The submitter's recheck set. -/
def K (s : Sym) : Prop := s ≠ .lex

theorem K_closed_changed : ∀ s, onlyParse s = true → K s := by
  intro s; cases s <;> simp [onlyParse, K]

theorem K_closed_deps : ∀ s t, Deps dep s t → K t → K s := by
  intro s t; cases s <;> cases t <;> simp [Deps, dep, parent, K]

def reversed : Sym → Stage := fun _ => List.reverse

theorem good_change_admitted : ∀ s, Q s (sem (update old onlyParse reversed) s) := by
  refine closed_witness_sound K K_closed_changed K_closed_deps sem_local old_good ?_
  intro s _
  cases s <;> intro xs <;>
    simp [Q, sem, run, step, parent, dep, old, update, onlyParse, reversed, sum_rev]

theorem lex_not_rerun (new : Sym → Stage) :
    sem (update old onlyParse new) .lex = sem old .lex :=
  outside_closed_unchanged K K_closed_changed K_closed_deps sem_local .lex (by simp [K])

def dropZeros : Sym → Stage := fun _ => List.filter (· ≠ 0)

theorem bad_change :
    Q .parse (sem (update old onlyParse dropZeros) .parse) ∧
      ¬ Q .docs (sem (update old onlyParse dropZeros) .docs) ∧
      Cone (Deps dep) onlyParse .docs := by
  refine ⟨?_, ?_, ?_⟩
  · intro xs
    simp [sem, run, step, parent, dep, old, update, onlyParse, dropZeros]
    induction xs with
    | nil => rfl
    | cons x xs ih => by_cases hx : x = 0 <;> simp [List.filter, hx, ih]
  · intro h
    have := h [0]
    simp [sem, run, step, parent, dep, old, update, onlyParse, dropZeros] at this
  · exact reach_cone ⟨.parse, .step (show Deps dep .docs .parse by rfl) (.refl _), rfl⟩

end Family.Examples.CompilerPass
