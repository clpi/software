import Std

namespace MerkleRepair

inductive Tree (α : Type) : Nat → Type where
  | leaf (value : α) : Tree α 0
  | fork (left right : Tree α h) : Tree α (h+1)

inductive Path : Nat → Type where
  | here : Path 0
  | left (rest : Path h) : Path (h+1)
  | right (rest : Path h) : Path (h+1)

inductive Cache (δ : Type) : Nat → Type where
  | leaf (digest : δ) : Cache δ 0
  | fork (digest : δ) (left right : Cache δ h) : Cache δ (h+1)

def root : Cache δ h → δ
  | .leaf d | .fork d _ _ => d

variable (leafHash : α → δ) (joinHash : δ → δ → δ)

def node (l r : Cache δ h) := Cache.fork (joinHash (root l) (root r)) l r
-- Return the constructed cache together with the number of hash operations.
def build : Tree α h → Cache δ h × Nat
  | .leaf x => (.leaf (leafHash x), 1)
  | .fork l r =>
    let (lc, lw) := build l
    let (rc, rw) := build r
    (node joinHash lc rc, lw + rw + 1)

def fullWork : Nat → Nat | 0 => 1 | h+1 => 1 + 2 * fullWork h

theorem build_cost (t : Tree α h) : (build leafHash joinHash t).2 = fullWork h := by
  induction t with
  | leaf => rfl
  | fork l r hl hr => simp only [build,fullWork,hl,hr]; omega

def edit : Path h → Tree α h → α → Tree α h
  | .here, .leaf _, x => .leaf x
  | .left p, .fork l r, x => .fork (edit p l x) r
  | .right p, .fork l r, x => .fork l (edit p r x)

-- Each call returns the cache and the fresh receipt levels, one per hash.
def repair : Path h → Cache δ h → α → Cache δ h × List Nat
  | .here, .leaf _, x => (.leaf (leafHash x), [0])
  | @Path.left d p, .fork _ l r, x =>
    let (child, receipts) := repair p l x
    (node joinHash child r, (d+1) :: receipts)
  | @Path.right d p, .fork _ l r, x =>
    let (child, receipts) := repair p r x
    (node joinHash l child, (d+1) :: receipts)

theorem clean_equivalence (p : Path h) (t : Tree α h) (x : α) :
    (repair leafHash joinHash p (build leafHash joinHash t).1 x).1 =
      (build leafHash joinHash (edit p t x)).1 := by
  induction p with
  | here => cases t; rfl
  | left p ih => cases t; simp [build,repair,edit,node] at *; simp [ih]
  | right p ih => cases t; simp [build,repair,edit,node] at *; simp [ih]

-- The audit contract requires a fresh receipt at the leaf and each ancestor.
def levels : Path h → List Nat
  | .here => [0]
  | @Path.left d p | @Path.right d p => (d+1) :: levels p

theorem repair_trace (p : Path h) (c : Cache δ h) (x : α) :
    (repair leafHash joinHash p c x).2 = levels p := by
  induction p with
  | here => cases c; rfl
  | left p ih => cases c; simp [repair,levels,ih]
  | right p ih => cases c; simp [repair,levels,ih]

theorem levels_exact (p : Path h) : levels p = (List.range (h+1)).reverse := by
  induction p with
  | here => rfl
  | left p ih => simp [levels, ih, List.range_succ]
  | right p ih => simp [levels, ih, List.range_succ]

private theorem size_floor (n : Nat) (work : List Nat)
    (covers : ∀ i < n, i ∈ work) : n ≤ work.length := by
  induction n generalizing work with
  | zero => omega
  | succ n ih =>
    have hn := covers n (by omega)
    have smaller := ih (work.erase n) (fun i hi =>
      (List.mem_erase_of_ne (Nat.ne_of_lt hi)).mpr (covers i (by omega)))
    rw [List.length_erase_of_mem hn] at smaller
    have positive := List.length_pos_of_mem hn
    omega

theorem least_receipts (p : Path h) (work : List Nat)
    (covers : ∀ i ∈ levels p, i ∈ work) : (levels p).length ≤ work.length := by
  rw [levels_exact] at *
  simp only [List.length_reverse, List.length_range]
  exact size_floor _ _ (fun i hi => covers i (by simpa using hi))

def leftmost : (h : Nat) → Path h | 0 => .here | h+1 => .left (leftmost h)

theorem before_after : fullWork 10 = 2047 ∧ (levels (leftmost 10)).length = 11 := by decide
theorem leaf_only_fails : 10 ∈ levels (leftmost 10) ∧ 10 ∉ [0] := by decide

#eval (fullWork 10, (levels (leftmost 10)).length)
#print axioms build_cost
#print axioms repair_trace
#print axioms clean_equivalence
#print axioms levels_exact
#print axioms least_receipts
#print axioms before_after
#print axioms leaf_only_fails
end MerkleRepair
