import Std

namespace RangeLedger.SignedStitch

structure Receipt where
  start : Nat
  stop : Nat
  value : Int
  deriving DecidableEq, Repr

def valid (p : Nat → Int) (r : Receipt) := r.value = p r.stop - p r.start
def rev (r : Receipt) : Receipt := ⟨r.stop,r.start,-r.value⟩
def stitch (a b : Receipt) : Option Receipt :=
  if a.stop = b.start then some ⟨a.start,b.stop,a.value+b.value⟩ else none

theorem reverse_valid (h : valid p r) : valid p (rev r) := by
  simp [valid,rev] at *; omega

theorem stitch_valid (ha : valid p a) (hb : valid p b) (ok : stitch a b = some c) :
    valid p c ∧ c.start = a.start ∧ c.stop = b.stop := by
  unfold stitch at ok
  split at ok
  next eq =>
    cases ok
    refine ⟨?_,rfl,rfl⟩
    simp only [valid] at *; rw [ha,hb,eq]; omega
  next => contradiction

def chain : Receipt → List Receipt → Option Receipt
  | acc, [] => some acc
  | acc, r::rs => (stitch acc r).bind (fun next => chain next rs)

theorem chain_valid (rs : List Receipt) (hs : ∀ r ∈ rs, valid p r)
    (acc : Receipt) (ha : valid p acc) (out : Receipt) (ok : chain acc rs = some out) :
    valid p out := by
  induction rs generalizing acc with
  | nil => cases ok; exact ha
  | cons r rs ih =>
    cases h : stitch acc r with
    | none => simp [chain,h] at ok
    | some next =>
      exact ih (fun x hx => hs x (by simp [hx])) next
        (stitch_valid ha (hs r (by simp)) h).1 (by simpa [chain,h] using ok)

def a : Receipt := ⟨0,3072,120⟩
def b : Receipt := ⟨1024,3072,50⟩
def c : Receipt := ⟨1024,4096,90⟩
theorem before_after : chain a [rev b,c] = some ⟨0,4096,160⟩ ∧ chain a [b,c] = none := by decide
#eval chain a [rev b,c]
#print axioms chain_valid
#print axioms before_after
end RangeLedger.SignedStitch
