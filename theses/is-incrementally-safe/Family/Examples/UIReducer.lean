import Family.Dataflow

/-!
# Worked example 6: a UI reducer

A Redux-style store. Actions add or remove items or clear the cart. Components: `reducer`
(the cart count after each action), `total` (selector), `badge` (shows the count), `checkout`
(the checkout button is enabled exactly when the cart is non-empty), and `theme`, which is
unrelated.

The reducer's own spec is its unit test: one state per action, and the count is zero after a
`clear`. Downstream specs compare against the reference reducer.

* `good_change_admitted`: the reducer is rewritten with an accumulator (`accRun_eq`).
  Rechecking the cone admits the release; `theme` is not re-run.
* `bad_change`: the reducer starts treating `add 0` (a missing quantity) as `add 1`. Its unit
  spec still holds (`bump_spec`), so a changed-only check admits it. The checkout button is now
  enabled on an empty cart after `add 0`. The button is in the cone, so the cone check refuses.

Premises: `Local` is `dataflow_local`; the reference reducer is the trusted spec.
-/
namespace Family.Examples.UIReducer

open Family.Dataflow Family.Selection SoftwareIsIncrementallySafe.OrderedIncrement

inductive Act where
  | add (n : Nat)
  | remove (n : Nat)
  | clear
  deriving DecidableEq, Repr

def apply (c : Nat) : Act → Nat
  | .add n => c + n
  | .remove n => c - n
  | .clear => 0

/-- Reference reducer: the count after each action. -/
def refRun : Nat → List Act → List Nat
  | _, [] => []
  | c, a :: as => apply c a :: refRun (apply c a) as

def accRun (c : Nat) (acc : List Nat) : List Act → List Nat
  | [] => acc.reverse
  | a :: as => accRun (apply c a) (apply c a :: acc) as

theorem accRun_eq : ∀ as c acc, accRun c acc as = acc.reverse ++ refRun c as
  | [], _, _ => by simp [accRun, refRun]
  | a :: as, c, acc => by simp [accRun, refRun, accRun_eq as]

def applyBump (c : Nat) : Act → Nat
  | .add 0 => c + 1
  | a => apply c a

def bumpRun : Nat → List Act → List Nat
  | _, [] => []
  | c, a :: as => applyBump c a :: bumpRun (applyBump c a) as

/-- The reducer's unit spec: one state per action, zero after `clear`. -/
def UnitSpec (r : List Act → List Nat) : Prop :=
  ∀ as, (r as).length = as.length ∧ ∀ i : Nat, as[i]? = some Act.clear → (r as)[i]? = some 0

theorem run_unit (f : Nat → Act → Nat) (hf : ∀ c, f c .clear = 0)
    (run : Nat → List Act → List Nat)
    (h0 : ∀ c, run c [] = []) (h1 : ∀ c a as, run c (a :: as) = f c a :: run (f c a) as) :
    ∀ as c, (run c as).length = as.length ∧
      ∀ i : Nat, as[i]? = some Act.clear → (run c as)[i]? = some 0
  | [], c => by simp [h0]
  | a :: as, c => by
    have ih := run_unit f hf run h0 h1 as (f c a)
    refine ⟨by simp [h1, ih.1], ?_⟩
    intro i hi
    cases i with
    | zero => simp at hi; simp [h1, hi, hf]
    | succ i => simp at hi; simp [h1]; exact ih.2 i hi

theorem ref_unit : ∀ as c, (refRun c as).length = as.length ∧
    ∀ i : Nat, as[i]? = some Act.clear → (refRun c as)[i]? = some 0 :=
  run_unit apply (fun _ => rfl) refRun (fun _ => rfl) (fun _ _ _ => rfl)

theorem bump_spec : ∀ as c, (bumpRun c as).length = as.length ∧
    ∀ i : Nat, as[i]? = some Act.clear → (bumpRun c as)[i]? = some 0 :=
  run_unit applyBump (fun _ => rfl) bumpRun (fun _ => rfl) (fun _ _ _ => rfl)

inductive Sym where
  | reducer | total | badge | checkout | theme
  deriving DecidableEq, Repr

def parent : Sym → Option Sym
  | .total => some .reducer
  | .badge => some .total
  | .checkout => some .total
  | _ => none

def dep (s t : Sym) : Bool := parent s == some t

abbrev Beh := List Act → List Nat
abbrev Code := Beh → Beh

def step (s : Sym) (c : Code) (f : Sym → Beh) : Beh :=
  match parent s with
  | none => c (fun _ => [])
  | some p => c (f p)

def sem (I : Sym → Code) (s : Sym) : Beh := run dep step (fun _ => []) I 3 s

def enabled (n : Nat) : Nat := if n = 0 then 0 else 1

def Q : Sym → Beh → Prop
  | .reducer, b => UnitSpec b
  | .total, b => ∀ as, b as = refRun 0 as
  | .badge, b => ∀ as, b as = (refRun 0 as).map (min 99)
  | .checkout, b => ∀ as, b as = (refRun 0 as).map enabled
  | .theme, b => ∀ as, b as = []

def old : Sym → Code
  | .reducer => fun _ => refRun 0
  | .total => fun f => f
  | .badge => fun f as => (f as).map (min 99)
  | .checkout => fun f as => (f as).map enabled
  | .theme => fun _ _ => []

theorem sem_local : Local (Deps dep) sem := dataflow_local dep step _ 3

theorem old_good : ∀ s, Q s (sem old s) := by
  intro s; cases s
  · intro as; simpa [sem, run, step, parent, dep, old] using ref_unit as 0
  all_goals intro as; simp [sem, run, step, parent, dep, old]

def onlyReducer : Sym → Bool := fun s => s == .reducer

def K (s : Sym) : Prop := s ≠ .theme

theorem K_changed : ∀ s, onlyReducer s = true → K s := by
  intro s; cases s <;> simp [onlyReducer, K]

theorem K_deps : ∀ s t, Deps dep s t → K t → K s := by
  intro s t; cases s <;> cases t <;> simp [Deps, dep, parent, K]

def withAcc : Sym → Code := fun _ _ => accRun 0 []

theorem good_change_admitted : ∀ s, Q s (sem (update old onlyReducer withAcc) s) := by
  refine closed_witness_sound K K_changed K_deps sem_local old_good ?_
  intro s _
  cases s
  · intro as; simpa [sem, run, step, parent, dep, update, onlyReducer, withAcc, accRun_eq]
      using ref_unit as 0
  all_goals intro as; simp [sem, run, step, parent, dep, old, update, onlyReducer, withAcc,
    accRun_eq]

theorem theme_not_rerun (new : Sym → Code) :
    sem (update old onlyReducer new) .theme = sem old .theme :=
  outside_closed_unchanged K K_changed K_deps sem_local .theme (by simp [K])

def bumped : Sym → Code := fun _ _ => bumpRun 0

theorem bad_change :
    Q .reducer (sem (update old onlyReducer bumped) .reducer) ∧
      ¬ Q .checkout (sem (update old onlyReducer bumped) .checkout) ∧
      Cone (Deps dep) onlyReducer .checkout := by
  refine ⟨?_, ?_, ?_⟩
  · intro as; simpa [sem, run, step, parent, dep, update, onlyReducer, bumped] using bump_spec as 0
  · intro h
    have := h [.add 0]
    simp [sem, run, step, parent, dep, update, onlyReducer, bumped, old, bumpRun, refRun,
      applyBump, apply, enabled] at this
  · exact reach_cone ⟨.reducer, .step (show Deps dep .checkout .total by rfl)
      (.step (show Deps dep .total .reducer by rfl) (.refl _)), rfl⟩

end Family.Examples.UIReducer
