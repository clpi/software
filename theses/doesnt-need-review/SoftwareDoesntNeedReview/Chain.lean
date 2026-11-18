import SoftwareDoesntNeedReview.Certifier

namespace SoftwareDoesntNeedReview

namespace Chain.Quantifiable

structure Execution where
  id : Nat
deriving DecidableEq, Repr

structure Witness where
  exec : Nat
  events : Nat
deriving DecidableEq, Repr

def Witnessed (e : Execution) (w : Witness) : Prop :=
  w.exec = e.id

def recorded (valid : Witness → Bool) (ledger : List Witness) (e : Execution) : Bool :=
  ledger.any (fun w => valid w && decide (w.exec = e.id))

structure PlatformPremise (valid : Witness → Bool) (ledger : List Witness)
    (roster : List Execution) where
  sensorBelow : Prop
  sensorBelowHolds : sensorBelow
  ledgerAppendOnly : Prop
  ledgerAppendOnlyHolds : ledgerAppendOnly
  mediated : ∀ e, e ∈ roster → recorded valid ledger e = true

theorem coverage {valid : Witness → Bool} {ledger : List Witness}
    {roster : List Execution} (P : PlatformPremise valid ledger roster) :
    ∀ e, e ∈ roster → recorded valid ledger e = true :=
  P.mediated

theorem unrestricted_witness (e : Execution) : ∃ w : Witness, Witnessed e w :=
  ⟨⟨e.id, 0⟩, rfl⟩

def missing (valid : Witness → Bool) (ledger : List Witness) (roster : List Execution) :
    List Execution :=
  roster.filter (fun e => !recorded valid ledger e)

theorem missing_empty (valid : Witness → Bool) (roster : List Execution) :
    missing valid [] roster = roster := by
  induction roster with
  | nil => rfl
  | cons e es ih =>
    simp [missing, recorded, List.filter, ih]

end Chain.Quantifiable

namespace Chain.Optimality

def noWorse (cand inc : Nat × Nat) : Prop :=
  cand.1 ≤ inc.1 ∧ cand.2 ≤ inc.2

def acceptsGuarded (sameContext : Bool) (droppedBehavior : Bool)
    (cand inc : Nat × Nat) : Prop :=
  sameContext = true ∧ droppedBehavior = false ∧ noWorse cand inc

theorem acceptsGuarded_iff (sameContext droppedBehavior : Bool) (cand inc : Nat × Nat) :
    acceptsGuarded sameContext droppedBehavior cand inc ↔
      sameContext = true ∧ droppedBehavior = false ∧ noWorse cand inc :=
  Iff.rfl

end Chain.Optimality

namespace Chain.Composable

def qualified (w : List (Sym × Ax)) (R : Release) : Bool :=
  w.all fun (s, a) => behaviorAt R s a == some Status.ok

theorem qualified_append (w1 w2 : List (Sym × Ax)) (R : Release) :
    qualified (w1 ++ w2) R = (qualified w1 R && qualified w2 R) := by
  induction w1 with
  | nil => simp [qualified]
  | cons p ps ih =>
    cases p with
    | mk s a =>
      simp [qualified, List.all, ih, Bool.and_assoc]

theorem qualified_implies_accept :
    ∀ (w : List (Sym × Ax)) (R : Release),
      qualified w R = true → firstRefusal w R = CertVerdict.accept
  | [], _, _ => rfl
  | (s, a) :: ps, R, h => by
    have hpair :
        ((behaviorAt R s a == some Status.ok) && qualified ps R) = true := by
      simpa [qualified] using h
    cases hok : (behaviorAt R s a == some Status.ok) <;>
      cases hrest : qualified ps R <;> simp [hok, hrest] at hpair
    have hbad : (behaviorAt R s a == some Status.bad) = false := by
      cases hbeh : behaviorAt R s a with
      | none => rfl
      | some st =>
        cases st with
        | ok => rfl
        | bad =>
          have htrue : (Status.bad == Status.ok) = true := by simpa [hbeh] using hok
          have hfalse : (Status.bad == Status.ok) = false := rfl
          rw [hfalse] at htrue
          cases htrue
    simp [firstRefusal, hbad]
    exact qualified_implies_accept ps R hrest

end Chain.Composable

namespace Chain.Certifiable

theorem extensive (w w' : List (Sym × Ax)) (R : Release) (s : Sym) (a : Ax)
    (hsub : ∀ s' a', watchedHas w s' a' = true → watchedHas w' s' a' = true)
    (hw : watchedHas w s a = true)
    (hb : (behaviorAt R s a == some Status.bad) = true) :
    refusesCell w' R s a = true :=
  refuses_of_mem w' R s a (hsub s a hw) hb

end Chain.Certifiable

namespace Chain.Regress

def regressed (base cand : Release) (w : List (Sym × Ax)) : List (Sym × Ax) :=
  w.filter fun (s, a) =>
    behaviorAt base s a == some Status.ok && behaviorAt cand s a == some Status.bad

def verdict (w : List (Sym × Ax)) (base cand : Release) : CertVerdict :=
  match regressed base cand w with
  | [] => CertVerdict.accept
  | (s, a) :: _ => CertVerdict.refuse s a

end Chain.Regress

namespace Chain.Safe

def verdict (w : List (Sym × Ax)) (R : Release) : CertVerdict :=
  firstRefusal w R

end Chain.Safe

end SoftwareDoesntNeedReview
