import SoftwareDoesntNeedReview.Certifier
import SoftwareIsComposable.Admission

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

namespace Chain.Certifiable

theorem extensive (w w' : List (Sym × Ax)) (R : Release) (s : Sym) (a : Ax)
    (hsub : ∀ s' a', watchedHas w s' a' = true → watchedHas w' s' a' = true)
    (hw : watchedHas w s a = true)
    (hb : (behaviorAt R s a == some Status.bad) = true) :
    refusesCell w' R s a = true :=
  refuses_of_mem w' R s a (hsub s a hw) hb

def growBehaviors (p : SoftwareIsComposable.SymbolProfile) (extra : List Nat) :
    SoftwareIsComposable.SymbolProfile :=
  { p with behaviors := p.behaviors ++ extra }

theorem extensive_equiv (old new : SoftwareIsComposable.SymbolProfile) (extra : List Nat)
    (hsub : ∀ b ∈ extra, b ∈ new.behaviors) :
    SoftwareIsComposable.symbolAdmitted old (growBehaviors new extra) = true ↔
      SoftwareIsComposable.symbolAdmitted old new = true := by
  constructor
  · intro h
    have hadm := SoftwareIsComposable.symbolAdmitted_iff.mp h
    apply SoftwareIsComposable.symbolAdmitted_iff.mpr
    refine ⟨hadm.sameId, hadm.validOld, hadm.validNew, ?_, hadm.costLen, hadm.costHi⟩
    intro b hb
    rcases List.mem_append.mp (hadm.keeps b hb) with h1 | h2
    · exact h1
    · exact hsub b h2
  · intro h
    have hadm := SoftwareIsComposable.symbolAdmitted_iff.mp h
    apply SoftwareIsComposable.symbolAdmitted_iff.mpr
    refine ⟨hadm.sameId, hadm.validOld, hadm.validNew, ?_, hadm.costLen, hadm.costHi⟩
    intro b hb
    exact List.mem_append.mpr (Or.inl (hadm.keeps b hb))

end Chain.Certifiable

namespace Chain.Regress

def regressed (base cand : Release) (w : List (Sym × Ax)) : List (Sym × Ax) :=
  w.filter fun (s, a) =>
    behaviorAt base s a == some Status.ok && behaviorAt cand s a == some Status.bad

def verdict (w : List (Sym × Ax)) (base cand : Release) : CertVerdict :=
  match regressed base cand w with
  | [] => CertVerdict.accept
  | (s, a) :: _ => CertVerdict.refuse s a

def preserved (old new : SoftwareIsComposable.SymbolProfile) : Bool :=
  old.behaviors.all fun b => new.behaviors.contains b

def costHeld (old new : SoftwareIsComposable.SymbolProfile) : Bool :=
  (old.costs.zip new.costs).all fun x => decide (x.2.hi ≤ x.1.hi)

def behaviorRegressed (old new : SoftwareIsComposable.SymbolProfile) : Bool :=
  !preserved old new

def costRegressed (old new : SoftwareIsComposable.SymbolProfile) : Bool :=
  !costHeld old new

theorem regress_equiv (old new : SoftwareIsComposable.SymbolProfile)
    (hid : old.id = new.id)
    (hvO : ∀ b ∈ old.costs, b.lo ≤ b.hi)
    (hvN : ∀ b ∈ new.costs, b.lo ≤ b.hi)
    (hlen : old.costs.length = new.costs.length) :
    (behaviorRegressed old new || costRegressed old new) = true ↔
      SoftwareIsComposable.symbolAdmitted old new = false := by
  have hvo : old.costs.all (fun b => decide (b.lo ≤ b.hi)) = true :=
    List.all_eq_true.mpr fun b hb => decide_eq_true (hvO b hb)
  have hvn : new.costs.all (fun b => decide (b.lo ≤ b.hi)) = true :=
    List.all_eq_true.mpr fun b hb => decide_eq_true (hvN b hb)
  have hidb : decide (old.id = new.id) = true := decide_eq_true hid
  have hlenb : decide (old.costs.length = new.costs.length) = true := decide_eq_true hlen
  have hsplit :
      SoftwareIsComposable.symbolAdmitted old new =
        (preserved old new && costHeld old new) := by
    simp [SoftwareIsComposable.symbolAdmitted, preserved, costHeld, hidb, hvo, hvn, hlenb,
      Bool.and_true, Bool.true_and]
  have hbeh : behaviorRegressed old new = !preserved old new := rfl
  have hcost : costRegressed old new = !costHeld old new := rfl
  rw [hsplit, hbeh, hcost]
  cases preserved old new <;> cases costHeld old new <;> simp

end Chain.Regress

namespace Chain.Safe

def verdict (w : List (Sym × Ax)) (R : Release) : CertVerdict :=
  firstRefusal w R

def preserved (old new : SoftwareIsComposable.SymbolProfile) : Bool :=
  Chain.Regress.preserved old new

theorem safe_equiv (old new : SoftwareIsComposable.SymbolProfile) :
    preserved old new = true ↔
      SoftwareIsComposable.accepts old.behaviors new.behaviors = true := by
  simp [preserved, Chain.Regress.preserved, SoftwareIsComposable.accepts,
    List.all_eq_true, List.contains_iff, decide_eq_true_iff]

theorem safe_of_admitted {old new : SoftwareIsComposable.SymbolProfile}
    (h : SoftwareIsComposable.SymbolAdmitted old new) :
    preserved old new = true :=
  (safe_equiv old new).mpr ((SoftwareIsComposable.accepts_iff).mpr h.keeps)

end Chain.Safe

end SoftwareDoesntNeedReview
