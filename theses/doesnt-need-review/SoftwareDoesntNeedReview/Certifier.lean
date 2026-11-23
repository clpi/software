import SoftwareDoesntNeedReview.Profile

namespace SoftwareDoesntNeedReview

inductive CertVerdict where
  | accept
  | refuse (symbol : Sym) (axis : Ax)
deriving DecidableEq, BEq, Repr

def watchedHas : List (Sym × Ax) → Sym → Ax → Bool
  | [], _, _ => false
  | (s', a') :: rest, s, a => (s' == s && a' == a) || watchedHas rest s a

def refusesCell : List (Sym × Ax) → Release → Sym → Ax → Bool
  | [], _, _, _ => false
  | (s', a') :: rest, R, s, a =>
      ((s' == s && a' == a) && behaviorAt R s a == some Status.bad) || refusesCell rest R s a

theorem refuses_of_mem :
    ∀ (w : List (Sym × Ax)) (R : Release) (s : Sym) (a : Ax),
      watchedHas w s a = true → (behaviorAt R s a == some Status.bad) = true →
        refusesCell w R s a = true
  | [], _, _, _, hw, _ => by simp [watchedHas] at hw
  | (s', a') :: rest, R, s, a, hw, hb => by
    have hOr : (s' == s && a' == a) = true ∨ watchedHas rest s a = true := by
      simpa [watchedHas, Bool.or_eq_true] using hw
    cases hOr with
    | inl hhead =>
      simp [refusesCell, hhead, hb]
    | inr hrest =>
      have ih := refuses_of_mem rest R s a hrest hb
      simp [refusesCell, ih]

def badRefusals (w : List (Sym × Ax)) (R : Release) : List (Sym × Ax) :=
  w.filter fun (s, a) => behaviorAt R s a == some Status.bad

def firstRefusal : List (Sym × Ax) → Release → CertVerdict
  | [], _ => CertVerdict.accept
  | (s, a) :: rest, R =>
    if behaviorAt R s a == some Status.bad then CertVerdict.refuse s a
    else firstRefusal rest R

def rowsOf (w : List (Sym × Ax)) (R : Release) : List (Sym × Ax × Option Status) :=
  w.map fun (s, a) => (s, a, behaviorAt R s a)

def statusesAlong : List (Sym × Ax) → Release → Option (List Status)
  | [], _ => some []
  | (s, a) :: rest, R =>
    match behaviorAt R s a with
    | none => none
    | some st =>
      match statusesAlong rest R with
      | none => none
      | some xs => some (st :: xs)

structure Test where
  symbol : Sym
  axis : Ax
  reads : List (Sym × Ax)
  pred : List Status → Bool

def testFires (t : Test) (R : Release) : Bool :=
  match statusesAlong t.reads R with
  | some st => t.pred st
  | none => false

def testRefusals (ts : List Test) (R : Release) : List (Sym × Ax) :=
  ts.filterMap fun t => if testFires t R then some (t.symbol, t.axis) else none

def namesRefusal (ts : List Test) (R : Release) (s : Sym) (a : Ax) : Bool :=
  ts.any fun t => t.symbol == s && t.axis == a && testFires t R

structure Certifier where
  watched : List (Sym × Ax)
  tests : List Test

def install (C : Certifier) (t : Test) : Certifier :=
  { C with tests := t :: C.tests }

structure Facts where
  rows : List (Sym × Ax × Option Status)
  refusals : List (Sym × Ax)
deriving DecidableEq, Repr

def factsOf (C : Certifier) (R : Release) : Facts :=
  { rows := rowsOf C.watched R
    refusals := badRefusals C.watched R ++ testRefusals C.tests R }

theorem beq_self (s : Sym) : (s == s) = true := by
  cases s <;> rfl

theorem beq_self_ax (a : Ax) : (a == a) = true := by
  cases a <;> rfl

theorem profile_criterion_mechanizable (C : Certifier) (t : Test) (R : Release)
    (st : List Status) (hs : statusesAlong t.reads R = some st) (hp : t.pred st = true) :
    namesRefusal (install C t).tests R t.symbol t.axis = true := by
  have hsym := beq_self t.symbol
  have hax := beq_self_ax t.axis
  simp [install, namesRefusal, List.any, testFires, hs, hp, hsym, hax]

theorem mechanized_value_is_table_row (pred : List Status → Bool) (n : Nat)
    (st : List Status) (hlen : st.length = n) (hp : pred st = true) :
    ∃ row, row ∈ table pred n ∧ row.1 = st ∧ row.2 = true := by
  obtain ⟨row, hm, h1, h2⟩ := decided_on_finite_space pred n st hlen
  exact ⟨row, hm, h1, by rw [h2, hp]⟩

end SoftwareDoesntNeedReview
