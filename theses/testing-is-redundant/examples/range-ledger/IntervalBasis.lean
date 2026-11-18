import Std

namespace RangeLedger.IntervalBasis
abbrev Answer := Nat → Nat → Int
-- Domain is nonempty half-open intervals inside [0,n].
def additive (f : Answer) := ∀ a b c, a < b → b < c → f a c = f a b + f b c
def singletons (n : Nat) (f g : Answer) := ∀ i < n, f i (i+1) = g i (i+1)

theorem all_queries {f g : Answer} (hf : additive f) (hg : additive g)
    (basis : singletons n f g) (a d : Nat) (bound : a + d + 1 ≤ n) :
    f a (a+d+1) = g a (a+d+1) := by
  induction d with
  | zero => exact basis a (by omega)
  | succ d ih =>
    let b := a+d+1
    have ha : a < b := by dsimp [b]; omega
    change f a (b+1) = g a (b+1)
    rw [hf a b (b+1) ha (by omega),hg a b (b+1) ha (by omega),
      show f a b = g a b from ih (by omega),basis b (by dsimp [b]; omega)]

-- Omit the i-th unit query. A step in the prefix potential hides at exactly i.
def step (i x : Nat) : Int := if i < x then 1 else 0
def spike (i a b : Nat) := step i b - step i a
theorem independently_needed (i : Nat) :
    additive (spike i) ∧ spike i i (i+1) = 1 ∧ ∀ j, j ≠ i → spike i j (j+1) = 0 := by
  refine ⟨fun a b c _ _ => by unfold spike; omega, ?_, ?_⟩
  · simp [spike,step]
  · intro j ne
    unfold spike step
    split <;> split <;> omega

-- Merge the endpoint classes constrained by each probe. Each merge can remove
-- at most one original label, even if probes use endpoints outside the roster.
abbrev Edge := Nat × Nat
def classes : List Edge → (Nat → Nat) × List Nat
  | [] => (id,[])
  | (a,b)::es =>
    let (label,removed) := classes es
    (fun x => if label x = label b then label a else label x, label b :: removed)

private theorem edges_equal (es : List Edge) : ∀ e ∈ es, (classes es).1 e.1 = (classes es).1 e.2 := by
  induction es with
  | nil => simp
  | cons z es ih =>
    obtain ⟨a,b⟩ := z
    intro e he
    rcases List.mem_cons.mp he with rfl | ht
    · simp [classes]
    · simp only [classes,ih e ht]

private theorem survives (es : List Edge) (x : Nat) (live : x ∉ (classes es).2) :
    (classes es).1 x = x := by
  induction es with
  | nil => rfl
  | cons z es ih =>
    obtain ⟨a,b⟩ := z
    simp only [classes,List.mem_cons,not_or] at live
    simp [classes,ih live.2,live.1]

private theorem merge_count (es : List Edge) : (classes es).2.length = es.length := by
  induction es with
  | nil => rfl
  | cons e es ih => cases e; simp [classes,ih]

private theorem slots (n : Nat) (xs : List Nat) (h : ∀ i < n, i ∈ xs) : n ≤ xs.length := by
  induction n generalizing xs with
  | zero => omega
  | succ n ih =>
    have hn := h n (by omega)
    have small := ih (xs.erase n) (fun i hi =>
      (List.mem_erase_of_ne (Nat.ne_of_lt hi)).mpr (h i (by omega)))
    rw [List.length_erase_of_mem hn] at small
    have pos := List.length_pos_of_mem hn
    omega

theorem arbitrary_probe_floor (n : Nat) (probes : List Edge)
    (sufficient : ∀ p q : Nat → Int, (∀ e ∈ probes, p e.2-p e.1 = q e.2-q e.1) →
      ∀ i < n, p (i+1)-p i = q (i+1)-q i) : n ≤ probes.length := by
  let c := (classes probes).1
  have agreement : ∀ e ∈ probes, (0 : Int)-0 = (c e.2 : Int)-c e.1 := by
    intro e he; rw [show c e.1 = c e.2 from edges_equal probes e he]; omega
  have determined := sufficient (fun _ => 0) (fun i => (c i : Int)) agreement
  have same : ∀ i ≤ n, c i = c 0 := by
    intro i; induction i with
    | zero => simp
    | succ i ih =>
      intro hi
      have h := determined i (by omega)
      change (0 : Int)-0 = (c (i+1) : Int)-c i at h
      have t := ih (by omega)
      omega
  have lower := slots (n+1) (c 0 :: (classes probes).2) (by
    intro i hi
    by_cases dead : i ∈ (classes probes).2
    · exact List.mem_cons_of_mem _ dead
    · have eq := survives probes i dead
      exact List.mem_cons.mpr (Or.inl (eq.symm.trans (same i (by omega)))))
  simp only [List.length_cons,merge_count] at lower
  omega

#print axioms arbitrary_probe_floor
theorem counts : 4096 * 4097 / 2 = 8390656 := by decide
#print axioms all_queries
#print axioms independently_needed
end RangeLedger.IntervalBasis
