namespace SoftwareDoesntNeedReview

inductive Sym where
  | parse
  | serialize
deriving DecidableEq, BEq, Repr

inductive Ax where
  | roundtrip
  | unicode
  | bytes
deriving DecidableEq, BEq, Repr

inductive Status where
  | ok
  | bad
deriving DecidableEq, BEq, Repr

structure Cell where
  symbol : Sym
  axis : Ax
  status : Status
deriving DecidableEq, BEq, Repr

structure Release where
  cells : List Cell
deriving DecidableEq, BEq, Repr

def behaviorAt (R : Release) (s : Sym) (a : Ax) : Option Status :=
  match R.cells.find? (fun c => c.symbol == s && c.axis == a) with
  | some c => some c.status
  | none => none

theorem sym_complete (s : Sym) : s = Sym.parse ∨ s = Sym.serialize := by
  cases s <;> simp

theorem ax_complete (a : Ax) :
    a = Ax.roundtrip ∨ a = Ax.unicode ∨ a = Ax.bytes := by
  cases a <;> simp

theorem status_complete (s : Status) : s = Status.ok ∨ s = Status.bad := by
  cases s <;> simp

def assignments : Nat → List (List Status)
  | 0 => [[]]
  | n + 1 =>
    let rest := assignments n
    rest.map (fun xs => Status.ok :: xs) ++ rest.map (fun xs => Status.bad :: xs)

theorem map_length {α β : Type} (f : α → β) :
    ∀ l : List α, (l.map f).length = l.length
  | [] => rfl
  | _ :: xs => by simp [List.map, map_length f xs]

theorem assignments_length : ∀ n, (assignments n).length = 2 ^ n
  | 0 => rfl
  | n + 1 => by
    rw [assignments]
    simp only [List.length_append, map_length]
    rw [assignments_length n, Nat.pow_succ, Nat.mul_comm, Nat.two_mul]

theorem mem_append_left {α : Type} {a : α} {l r : List α} (h : a ∈ l) : a ∈ l ++ r := by
  induction l with
  | nil => cases h
  | cons x xs ih =>
    cases h with
    | head => exact List.Mem.head _
    | tail _ ht => exact List.Mem.tail _ (ih ht)

theorem mem_append_right {α : Type} {a : α} {l r : List α} (h : a ∈ r) : a ∈ l ++ r := by
  induction l with
  | nil => exact h
  | cons _ _ ih => exact List.Mem.tail _ (ih)

theorem mem_map {α β : Type} (f : α → β) {a : α} {l : List α} (h : a ∈ l) : f a ∈ l.map f := by
  induction l with
  | nil => cases h
  | cons x xs ih =>
    cases h with
    | head => exact List.Mem.head _
    | tail _ ht => exact List.Mem.tail _ (ih ht)

theorem length_cons_inj {st : Status} {xs : List Status} {n : Nat}
    (h : (st :: xs).length = n + 1) : xs.length = n := by
  simpa [List.length, Nat.succ_eq_add_one] using Nat.succ.inj (by simpa [List.length, Nat.succ_eq_add_one] using h)

theorem assignments_complete : ∀ n (st : List Status), st.length = n → st ∈ assignments n
  | 0, [], _ => by simp [assignments]
  | 0, _ :: _, h => by simp at h
  | _ + 1, [], h => by simp at h
  | n + 1, Status.ok :: xs, h => by
    have hx : xs ∈ assignments n := assignments_complete n xs (length_cons_inj h)
    rw [assignments]
    exact mem_append_left (mem_map (fun ys => Status.ok :: ys) hx)
  | n + 1, Status.bad :: xs, h => by
    have hx : xs ∈ assignments n := assignments_complete n xs (length_cons_inj h)
    rw [assignments]
    exact mem_append_right (mem_map (fun ys => Status.bad :: ys) hx)

theorem profile_space_finite (n : Nat) :
    (assignments n).length = 2 ^ n ∧ ∀ st, st.length = n → st ∈ assignments n :=
  ⟨assignments_length n, fun st h => assignments_complete n st h⟩

def table (pred : List Status → Bool) (n : Nat) : List (List Status × Bool) :=
  (assignments n).map fun st => (st, pred st)

theorem decided_on_finite_space (pred : List Status → Bool) (n : Nat) (st : List Status)
    (hlen : st.length = n) :
    ∃ row, row ∈ table pred n ∧ row.1 = st ∧ row.2 = pred st := by
  refine ⟨(st, pred st), ?_, rfl, rfl⟩
  exact mem_map (fun s => (s, pred s)) (assignments_complete n st hlen)

def predIsBad : List Status → Bool
  | Status.bad :: _ => true
  | _ => false

theorem profile_pred_total (pred : List Status → Bool) (st : List Status) :
    pred st = true ∨ pred st = false := by
  cases h : pred st <;> simp [h]

end SoftwareDoesntNeedReview
