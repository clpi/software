import SoftwareIsComposable.Incremental

open SoftwareIsComposable

namespace SoftwareIsIncrementallySafe

def parentsOf : List (Nat × Nat) → List Nat → List Nat
  | [], _ => []
  | e :: es, acc =>
    if acc.contains e.snd then e.fst :: parentsOf es acc else parentsOf es acc

def expand (deps : List (Nat × Nat)) (acc : List Nat) : List Nat :=
  acc ++ (parentsOf deps acc).filter (fun s => !acc.contains s)

def iterCone (deps : List (Nat × Nat)) (seeds : List Nat) : Nat → List Nat
  | 0 => seeds
  | n + 1 => expand deps (iterCone deps seeds n)

def coneExecOf (deps : List (Nat × Nat)) (seeds : List Nat) : List Nat :=
  iterCone deps seeds (deps.length + seeds.length + 1)

theorem expand_keeps {deps : List (Nat × Nat)} {acc : List Nat} {s : Nat}
    (h : s ∈ acc) : s ∈ expand deps acc := by
  simp [expand, List.mem_append, h]

theorem iter_mono {deps : List (Nat × Nat)} {seeds : List Nat} :
    ∀ {k n : Nat}, k ≤ n → ∀ {s : Nat},
      s ∈ iterCone deps seeds k → s ∈ iterCone deps seeds n := by
  intro k n hkn
  induction hkn with
  | refl => intro s hs; exact hs
  | step _ ih =>
    intro s hs
    rw [iterCone]
    exact expand_keeps (ih hs)

theorem parents_mem {deps : List (Nat × Nat)} {acc : List Nat} {s : Nat}
    (h : s ∈ parentsOf deps acc) : ∃ t, (s, t) ∈ deps ∧ t ∈ acc := by
  induction deps with
  | nil => cases h
  | cons e es ih =>
    rcases e with ⟨a, b⟩
    have hform : parentsOf ((a, b) :: es) acc =
        (if acc.contains b = true then a :: parentsOf es acc else parentsOf es acc) := rfl
    cases hcb : acc.contains b with
    | true =>
      have hmem : s ∈ a :: parentsOf es acc := by
        rw [hform, hcb] at h
        simpa using h
      cases hmem with
      | head => exact ⟨b, List.Mem.head _, List.contains_iff.mp hcb⟩
      | tail _ hs =>
        rcases ih hs with ⟨t, hdep, ht⟩
        exact ⟨t, List.Mem.tail _ hdep, ht⟩
    | false =>
      have hs : s ∈ parentsOf es acc := by
        rw [hform, hcb] at h
        simpa using h
      rcases ih hs with ⟨t, hdep, ht⟩
      exact ⟨t, List.Mem.tail _ hdep, ht⟩

theorem parents_edge {deps : List (Nat × Nat)} {acc : List Nat} {s t : Nat}
    (hedge : (s, t) ∈ deps) (ht : t ∈ acc) : s ∈ parentsOf deps acc := by
  induction deps with
  | nil => cases hedge
  | cons e es ih =>
    rcases e with ⟨a, b⟩
    have hform : parentsOf ((a, b) :: es) acc =
        (if acc.contains b = true then a :: parentsOf es acc else parentsOf es acc) := rfl
    rw [hform]
    cases hedge with
    | head =>
      have hc : acc.contains t = true := List.contains_iff.mpr ht
      rw [hc]
      simp
    | tail _ h =>
      cases hc : acc.contains b with
      | true =>
        simp
        exact Or.inr (ih h)
      | false =>
        simp
        exact ih h

theorem expand_edge {deps : List (Nat × Nat)} {acc : List Nat} {s t : Nat}
    (hedge : (s, t) ∈ deps) (ht : t ∈ acc) : s ∈ expand deps acc := by
  by_cases hs : s ∈ acc
  · exact expand_keeps hs
  · have hp := parents_edge hedge ht
    have hc : acc.contains s = false := by simpa [List.contains_iff] using hs
    simp [expand, List.mem_append, List.mem_filter]
    refine Or.inr ⟨hp, ?_⟩
    simpa [List.contains_iff] using hc

theorem added_from {deps : List (Nat × Nat)} {seeds : List Nat} {s : Nat} {k : Nat}
    (hs : s ∈ iterCone deps seeds (k + 1)) (hnot : ¬ s ∈ iterCone deps seeds k) :
    ∃ t, (s, t) ∈ deps ∧ t ∈ iterCone deps seeds k := by
  rw [iterCone, expand, List.mem_append] at hs
  cases hs with
  | inl h => exact (hnot h).elim
  | inr h =>
    rcases parents_mem (List.mem_filter.mp h).1 with ⟨t, hdep, ht⟩
    exact ⟨t, hdep, ht⟩

theorem mem_map_fst {deps : List (Nat × Nat)} {s t : Nat}
    (h : (s, t) ∈ deps) : s ∈ deps.map Prod.fst := by
  induction deps with
  | nil => cases h
  | cons _ es ih =>
    cases h with
    | head => simp
    | tail _ h => simp [ih h]

theorem nodup_subset_length {l c : List Nat} (nd : c.Nodup)
    (hsub : ∀ x, x ∈ c → x ∈ l) : c.length ≤ l.length := by
  induction c generalizing l with
  | nil => exact Nat.zero_le _
  | cons x xs ih =>
    have hx : x ∈ l := hsub x (List.Mem.head _)
    have hsplit := List.nodup_cons.mp nd
    have ihxs := ih (l := l.erase x) hsplit.2 (fun y hy =>
      (List.mem_erase_of_ne (fun heq => hsplit.1 (by subst heq; exact hy))).mpr
        (hsub y (List.Mem.tail _ hy)))
    have hlen := List.length_erase_of_mem hx
    have hpos : 0 < l.length := List.length_pos_of_mem hx
    have : xs.length + 1 ≤ (l.erase x).length + 1 := Nat.succ_le_succ ihxs
    rw [hlen, Nat.sub_add_cancel hpos] at this
    simpa [List.length_cons] using this

def leastFrom (p : Nat → Bool) (i fuel : Nat) : Nat :=
  match fuel with
  | 0 => i
  | n + 1 => if p i then i else leastFrom p (i + 1) n

theorem leastFrom_le (p : Nat → Bool) (i fuel : Nat) : leastFrom p i fuel ≤ i + fuel := by
  induction fuel generalizing i with
  | zero => simp [leastFrom]
  | succ n ih =>
    rw [leastFrom]
    cases hp : p i with
    | true => simp [hp]
    | false =>
      simp [hp]
      have := ih (i + 1)
      omega

theorem leastFrom_holds (p : Nat → Bool) (i fuel : Nat)
    (h : ∃ k, k ≤ fuel ∧ p (i + k) = true) : p (leastFrom p i fuel) = true := by
  induction fuel generalizing i with
  | zero =>
    rcases h with ⟨k, hk, hp⟩
    have hk0 : k = 0 := Nat.le_zero.mp hk
    subst hk0
    simpa [leastFrom] using hp
  | succ n ih =>
    rw [leastFrom]
    cases hpi : p i with
    | true => simp [hpi]
    | false =>
      simp [hpi]
      apply ih
      rcases h with ⟨k, hk, hp⟩
      cases k with
      | zero =>
        simp at hp
        rw [hpi] at hp
        cases hp
      | succ k =>
        exact ⟨k, by omega, by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hp⟩

theorem leastFrom_min (p : Nat → Bool) (i fuel j : Nat) (hj : i ≤ j)
    (hlt : j < leastFrom p i fuel) : p j = false := by
  induction fuel generalizing i with
  | zero =>
    simp [leastFrom] at hlt
    omega
  | succ n ih =>
    rw [leastFrom] at hlt
    cases hpi : p i with
    | true =>
      simp [hpi] at hlt
      omega
    | false =>
      simp [hpi] at hlt
      by_cases hji : j = i
      · simpa [hji] using hpi
      · exact ih (i + 1) (by omega) hlt

def memIter (deps : List (Nat × Nat)) (seeds : List Nat) (s : Nat) (n : Nat) : Bool :=
  (iterCone deps seeds n).contains s

theorem memIter_iff (deps : List (Nat × Nat)) (seeds : List Nat) (s : Nat) (n : Nat) :
    memIter deps seeds s n = true ↔ s ∈ iterCone deps seeds n := by
  simp [memIter, List.contains_iff]

theorem exists_spine (deps : List (Nat × Nat)) (seeds : List Nat) (n : Nat) :
    ∀ s, s ∈ iterCone deps seeds n → (∀ m, m < n → ¬ s ∈ iterCone deps seeds m) →
      ∃ c : List Nat, c.length = n + 1 ∧ c.Nodup ∧
        (∀ x, x ∈ c → x ∈ iterCone deps seeds n) ∧
        (∀ x, x ∈ c → x ∈ seeds ++ deps.map Prod.fst) :=
  Nat.strongRecOn (motive := fun n => ∀ s, s ∈ iterCone deps seeds n →
      (∀ m, m < n → ¬ s ∈ iterCone deps seeds m) →
      ∃ c : List Nat, c.length = n + 1 ∧ c.Nodup ∧
        (∀ x, x ∈ c → x ∈ iterCone deps seeds n) ∧
        (∀ x, x ∈ c → x ∈ seeds ++ deps.map Prod.fst)) n
    (fun n IH s hs hmin => by
      cases n with
      | zero =>
        refine ⟨[s], rfl, ?_, ?_, ?_⟩
        · apply List.nodup_cons.mpr
          constructor
          · intro h
            cases h
          · exact List.Pairwise.nil
        · intro x hx
          simp at hx
          subst hx
          simpa [iterCone] using hs
        · intro x hx
          simp at hx
          subst hx
          exact List.mem_append.mpr (Or.inl (by simpa [iterCone] using hs))
      | succ k =>
        have hnot : ¬ s ∈ iterCone deps seeds k := hmin k (Nat.lt_succ_self _)
        rcases added_from hs hnot with ⟨t, hedge, ht⟩
        let p := fun j => memIter deps seeds t j
        let m := leastFrom p 0 k
        have hm_le : m ≤ k := by
          have hle := leastFrom_le p 0 k
          simp [Nat.zero_add] at hle
          exact hle
        have hm_true : p m = true :=
          leastFrom_holds p 0 k ⟨k, by simp [Nat.zero_add], by
            have ht' := (memIter_iff deps seeds t k).mpr ht
            simpa [p, Nat.zero_add] using ht'⟩
        have hm : t ∈ iterCone deps seeds m := (memIter_iff deps seeds t m).mp hm_true
        have hmint : ∀ j, j < m → ¬ t ∈ iterCone deps seeds j := by
          intro j hj hin
          have htrue : p j = true := (memIter_iff deps seeds t j).mpr hin
          rw [leastFrom_min p 0 k j (Nat.zero_le _) hj] at htrue
          cases htrue
        have hsoon : s ∈ iterCone deps seeds (m + 1) := by
          rw [iterCone]
          exact expand_edge hedge hm
        have hleast : k + 1 ≤ m + 1 := by
          apply Classical.byContradiction
          intro hgt
          exact hmin (m + 1) (Nat.lt_of_not_le hgt) hsoon
        have heq : m = k := by omega
        rcases IH m (Nat.lt_of_le_of_lt hm_le (Nat.lt_succ_self k)) t hm hmint with
          ⟨c, hlen, hnd, hin, hsub⟩
        have hnotm : ¬ s ∈ iterCone deps seeds m := by simpa [heq] using hnot
        refine ⟨s :: c, ?_, ?_, ?_, ?_⟩
        · rw [List.length_cons, hlen]
          omega
        · exact List.nodup_cons.mpr ⟨fun hsin => hnotm (hin s hsin), hnd⟩
        · intro x hx
          cases hx with
          | head => exact hs
          | tail _ hxc =>
            exact iter_mono (Nat.le_succ_of_le hm_le) (hin x hxc)
        · intro x hx
          cases hx with
          | head => exact List.mem_append.mpr (Or.inr (mem_map_fst hedge))
          | tail _ hxc => exact hsub x hxc)

theorem cone_in_iter {deps : List (Nat × Nat)} {seeds : List Nat} {s : Nat}
    (h : InClosure deps seeds s) : ∃ n, s ∈ iterCone deps seeds n := by
  induction h with
  | seed hmem => exact ⟨0, by simpa [iterCone] using hmem⟩
  | step hdep _ ih =>
    rcases ih with ⟨n, hn⟩
    exact ⟨n + 1, by rw [iterCone]; exact expand_edge hdep hn⟩

theorem iter_cone_sound {deps : List (Nat × Nat)} {seeds : List Nat} (n : Nat)
    {s : Nat} (h : s ∈ iterCone deps seeds n) : InClosure deps seeds s := by
  induction n generalizing s with
  | zero =>
    simp [iterCone] at h
    exact InClosure.seed h
  | succ n ih =>
    rw [iterCone, expand, List.mem_append] at h
    cases h with
    | inl hs => exact ih hs
    | inr hs =>
      rcases parents_mem (List.mem_filter.mp hs).1 with ⟨t, hdep, ht⟩
      exact InClosure.step hdep (ih ht)

theorem coneExec_sound {deps : List (Nat × Nat)} {seeds : List Nat} {s : Nat}
    (h : s ∈ coneExecOf deps seeds) : InClosure deps seeds s :=
  iter_cone_sound _ (by
    have h' : s ∈ iterCone deps seeds (deps.length + seeds.length + 1) := by
      simpa [coneExecOf] using h
    exact h')

theorem coneExec_complete {deps : List (Nat × Nat)} {seeds : List Nat} {s : Nat}
    (h : InClosure deps seeds s) : s ∈ coneExecOf deps seeds := by
  rcases cone_in_iter h with ⟨n0, hn0⟩
  let p := fun j => memIter deps seeds s j
  let n := leastFrom p 0 n0
  have hn_true : p n = true :=
    leastFrom_holds p 0 n0 ⟨n0, by simp [Nat.zero_add], by
      have hn0' := (memIter_iff deps seeds s n0).mpr hn0
      simpa [p, Nat.zero_add] using hn0'⟩
  have hn : s ∈ iterCone deps seeds n := (memIter_iff deps seeds s n).mp hn_true
  have hmin : ∀ m, m < n → ¬ s ∈ iterCone deps seeds m := by
    intro m hm hin
    have htrue : p m = true := (memIter_iff deps seeds s m).mpr hin
    rw [leastFrom_min p 0 n0 m (Nat.zero_le _) hm] at htrue
    cases htrue
  rcases exists_spine deps seeds n s hn hmin with ⟨c, hlen, hnd, _, hsub⟩
  have hcard := nodup_subset_length hnd hsub
  have hfuel : n ≤ deps.length + seeds.length + 1 := by
    have hlen' : n + 1 ≤ seeds.length + deps.length := by
      simpa [hlen, List.length_append, List.length_map] using hcard
    omega
  exact iter_mono hfuel (by simpa [coneExecOf] using hn)

theorem coneExec_iff_affected {deps : List (Nat × Nat)} {seeds : List Nat} {s : Nat} :
    s ∈ coneExecOf deps seeds ↔
      HypergraphIncremental.Affected (hyper [] deps) (hyper seeds deps) s :=
  ⟨fun h => inClosure_iff_affected.mp (coneExec_sound h),
    fun h => coneExec_complete (inClosure_iff_affected.mpr h)⟩

def ClosureHyp (deps : List (Nat × Nat)) (seeds inspected : List Nat) : Prop :=
  ∀ s, InClosure deps seeds s → s ∈ inspected

theorem closureHyp_of_computed (deps : List (Nat × Nat)) (seeds : List Nat) :
    ClosureHyp deps seeds (coneExecOf deps seeds) :=
  fun _ hs => coneExec_complete hs

def releaseCalls (symbols : List Nat) : List (Nat × Nat) :=
  symbols.flatMap fun _ => []

theorem closure_from_release (symbols : List Nat) (changed : List Nat) :
    ClosureHyp (releaseCalls symbols) changed
      (coneExecOf (releaseCalls symbols) changed) :=
  closureHyp_of_computed _ _

abbrev configSym : Nat := 0

abbrev workerSym : Nat := 1

theorem f3_external_uses_closureHyp
    (hClo : ClosureHyp [(workerSym, configSym)] [configSym]
      (coneExecOf [(workerSym, configSym)] [configSym])) :
    workerSym ∈ coneExecOf [(workerSym, configSym)] [configSym] := by
  have hcone : InClosure [(workerSym, configSym)] [configSym] workerSym :=
    InClosure.step (callee := configSym) (by simp) (InClosure.seed (by simp))
  exact hClo workerSym hcone

theorem f3_external_instance :
    ClosureHyp [(workerSym, configSym)] [configSym]
      (coneExecOf [(workerSym, configSym)] [configSym]) :=
  closureHyp_of_computed _ _

theorem f3_config_in_cone :
    workerSym ∈ coneExecOf [(workerSym, configSym)] [configSym] :=
  f3_external_uses_closureHyp f3_external_instance

#print axioms coneExec_sound
#print axioms coneExec_complete
#print axioms coneExec_iff_affected
#print axioms closureHyp_of_computed
#print axioms closure_from_release
#print axioms f3_external_uses_closureHyp

end SoftwareIsIncrementallySafe
