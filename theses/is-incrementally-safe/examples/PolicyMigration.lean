import Std

namespace PolicyMigration

-- Acceptance policies may consume several independent qualification facts.
inductive Expr where
  | fact (key : Nat) | both (l r : Expr) | either (l r : Expr)
  deriving DecidableEq, Repr
abbrev Snapshot := Nat → Bool
def eval (env : Snapshot) : Expr → Bool
  | .fact k => env k
  | .both l r => eval env l && eval env r
  | .either l r => eval env l || eval env r
def reads : Expr → List Nat
  | .fact k => [k]
  | .both l r | .either l r => reads l ++ reads r

theorem frame (e : Expr) (a b : Snapshot) (h : ∀ k ∈ reads e, a k = b k) :
    eval a e = eval b e := by
  induction e with
  | fact k => exact h k (by simp [reads])
  | both l r hl hr =>
    simp only [eval, hl (fun k hk => h k (List.mem_append_left _ hk)),
      hr (fun k hk => h k (List.mem_append_right _ hk))]
  | either l r hl hr =>
    simp only [eval, hl (fun k hk => h k (List.mem_append_left _ hk)),
      hr (fun k hk => h k (List.mem_append_right _ hk))]

def reusable (a b : Snapshot) (old new : Expr) :=
  decide (old = new) && (reads old).all (fun k => a k == b k)
def refresh (a b : Snapshot) (old new : Expr) (cached : Bool) :=
  if reusable a b old new then cached else eval b new

theorem same_as_clean (a b : Snapshot) (old new : Expr) (cached : Bool)
    (valid : cached = eval a old) : refresh a b old new cached = eval b new := by
  unfold refresh
  split
  next hr =>
    simp [reusable, List.all_eq_true] at hr
    obtain ⟨rfl,h⟩ := hr
    exact valid.trans (frame old a b h)
  next => rfl

-- 0 = legacy approval, 1 = replacement approval, 2 = fixtures, 3 = docs.
open Expr
def previous := [both (fact 0) (fact 2), fact 2, either (fact 1) (fact 3), fact 3]
def current := [both (fact 1) (fact 2), fact 2, either (fact 1) (fact 3), fact 3]
def was (k : Nat) := k == 0 || k == 1 || k == 2
def now (k : Nat) := k == 0 || k == 2
def cache (a : Snapshot) (rules : List Expr) := rules.map (fun e => (e, eval a e))
def patch (a b : Snapshot) : List (Expr × Bool) → List Expr → List Bool
  | _, [] => []
  | [], ys => ys.map (eval b)
  | (x,v) :: xs, y :: ys => refresh a b x y v :: patch a b xs ys

theorem all_rows_exact (a b : Snapshot) (old new : List Expr) :
    patch a b (cache a old) new = new.map (eval b) := by
  induction new generalizing old with
  | nil => cases old <;> rfl
  | cons y ys ih =>
    cases old with
    | nil => rfl
    | cons x xs =>
      change refresh a b x y (eval a x) :: patch a b (cache a xs) ys = _
      rw [same_as_clean _ _ _ _ _ rfl, ih]
      rfl
def dirty := (previous.zip current).map (fun (x,y) => !reusable was now x y)

theorem before_after : previous.map (eval was) = [true,true,true,false] ∧
    dirty = [true,false,true,false] ∧
    patch was now (cache was previous) current = [false,true,false,false] ∧
    patch was now (cache was previous) current = current.map (eval now) := by decide

-- A rule-only edit changes the answer even if every source bit is unchanged.
theorem value_only_is_unsafe : eval now (previous[0]) = true ∧
    eval now (current[0]) = false := by decide

-- Any slot that is reused must keep its previous value. Both changed answers
-- therefore force a replacement even for checkers with a more selective rule.
theorem necessary_replacements (use0 use2 v0 v2 : Bool)
    (first : (if use0 then eval was previous[0] else v0) = eval now current[0])
    (third : (if use2 then eval was previous[2] else v2) = eval now current[2]) :
    use0 = false ∧ use2 = false := by
  cases use0 <;> cases use2 <;> simp_all +decide

#print axioms all_rows_exact
#print axioms necessary_replacements
#eval (dirty, previous.map (eval was), patch was now (cache was previous) current)
#print axioms frame
#print axioms same_as_clean
#print axioms before_after
#print axioms value_only_is_unsafe
end PolicyMigration
