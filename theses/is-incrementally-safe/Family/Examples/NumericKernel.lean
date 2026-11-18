import Family.Dataflow

/-!
# Worked example 3: a numeric kernel

Components: `dot` (the inner-product kernel), `norm` (squared norm, built on `dot`), `classify`
(a sign test on `dot`, e.g. a branch in a solver), `report` (what `classify` decided), and
`plot`, which is unrelated.

Specs: `dot` and `norm` must be within one unit of the exact value (a tolerance spec, the usual
form for floating-point kernels); `classify` and `report` must decide exactly as the exact sign
would.

* `good_change_admitted`: `dot` is rewritten as an accumulator loop (`loop_eq` proves it equals
  the exact sum for every input). Rechecking the cone admits the release; `plot` is not re-run.
* `bad_change`: `dot` picks up a bias of one unit (say, a rounding-mode change). The kernel still
  meets its tolerance spec, and so does `norm`, so a changed-only check admits it. `classify`
  flips its decision at `v = [1]`, `w = [-1]`, where the exact value is `-1`. This is the
  ill-conditioning failure: every kernel is within tolerance and a discrete decision downstream
  changes. The cone check refuses it.

Premises: `Local` is `dataflow_local`; integers stand for the exact arithmetic the tolerance is
measured against.
-/
namespace Family.Examples.NumericKernel

open Family.Dataflow Family.Selection SoftwareIsIncrementallySafe.OrderedIncrement

def exact : List Int → List Int → Int
  | x :: v, y :: w => x * y + exact v w
  | _, _ => 0

def loop (acc : Int) : List Int → List Int → Int
  | x :: v, y :: w => loop (acc + x * y) v w
  | _, _ => acc

theorem loop_eq : ∀ (v w : List Int) (acc : Int), loop acc v w = acc + exact v w
  | x :: v, y :: w, acc => by simp [loop, exact, loop_eq v w]; omega
  | [], _, acc => by simp [loop, exact]
  | _ :: _, [], acc => by simp [loop, exact]

inductive Sym where
  | dot | norm | classify | report | plot
  deriving DecidableEq, Repr

def parent : Sym → Option Sym
  | .norm => some .dot
  | .classify => some .dot
  | .report => some .classify
  | _ => none

def dep (s t : Sym) : Bool := parent s == some t

abbrev Beh := List Int → List Int → Int
abbrev Code := Beh → Beh

def step (s : Sym) (c : Code) (f : Sym → Beh) : Beh :=
  match parent s with
  | none => c (fun _ _ => 0)
  | some p => c (f p)

def sem (I : Sym → Code) (s : Sym) : Beh := run dep step (fun _ _ => 0) I 3 s

def Q : Sym → Beh → Prop
  | .dot, b => ∀ v w, b v w - exact v w ≤ 1 ∧ exact v w - b v w ≤ 1
  | .norm, b => ∀ v w, b v w - exact v v ≤ 1 ∧ exact v v - b v w ≤ 1
  | .classify, b => ∀ v w, b v w = if 0 ≤ exact v w then 1 else 0
  | .report, b => ∀ v w, b v w = if 0 ≤ exact v w then 1 else 0
  | .plot, b => ∀ v w, b v w = 0

def old : Sym → Code
  | .dot => fun _ => exact
  | .norm => fun d v _ => d v v
  | .classify => fun d v w => if 0 ≤ d v w then 1 else 0
  | .report => fun c => c
  | .plot => fun _ _ _ => 0

theorem sem_local : Local (Deps dep) sem := dataflow_local dep step _ 3

theorem old_good : ∀ s, Q s (sem old s) := by
  intro s; cases s <;> intro v w <;> simp [Q, sem, run, step, parent, dep, old]

def onlyDot : Sym → Bool := fun s => s == .dot

def K (s : Sym) : Prop := s ≠ .plot

theorem K_changed : ∀ s, onlyDot s = true → K s := by
  intro s; cases s <;> simp [onlyDot, K]

theorem K_deps : ∀ s t, Deps dep s t → K t → K s := by
  intro s t; cases s <;> cases t <;> simp [Deps, dep, parent, K]

def looped : Sym → Code := fun _ _ => loop 0

theorem good_change_admitted : ∀ s, Q s (sem (update old onlyDot looped) s) := by
  refine closed_witness_sound K K_changed K_deps sem_local old_good ?_
  intro s _
  cases s <;> intro v w <;>
    simp [Q, sem, run, step, parent, dep, old, update, onlyDot, looped, loop_eq]

theorem plot_not_rerun (new : Sym → Code) :
    sem (update old onlyDot new) .plot = sem old .plot :=
  outside_closed_unchanged K K_changed K_deps sem_local .plot (by simp [K])

def biased : Sym → Code := fun _ _ v w => exact v w + 1

theorem bad_change :
    Q .dot (sem (update old onlyDot biased) .dot) ∧
      Q .norm (sem (update old onlyDot biased) .norm) ∧
      ¬ Q .classify (sem (update old onlyDot biased) .classify) ∧
      Cone (Deps dep) onlyDot .classify := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v w; simp [sem, run, step, parent, dep, update, onlyDot, biased]; omega
  · intro v w; simp [sem, run, step, parent, dep, update, onlyDot, biased, old]; omega
  · intro h
    have := h [1] [-1]
    simp [sem, run, step, parent, dep, update, onlyDot, biased, old, exact] at this
  · exact reach_cone ⟨.dot, .step (show Deps dep .classify .dot by rfl) (.refl _), rfl⟩

end Family.Examples.NumericKernel
