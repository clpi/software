import SoftwareIsIncrementallySafe.Security

namespace SoftwareIsIncrementallySafe

open SoftwareIsComposable
open SoftwareIsIncrementallyCertifiable

inductive Verdict (α : Type) where
  | accept
  | refuse (symbol : α)
  deriving DecidableEq, Repr

structure ExecDelta where
  changed : List (String × List String)
  deps : List (String × String)
  inspect : List String
  symHigh : String → Bool
  obsHigh : String → Bool
  boundTime : Nat
  boundCompute : Nat

def changedSymbols (d : ExecDelta) : List String :=
  d.changed.map Prod.fst

def behaviorAfter (base : String → List String) (d : ExecDelta) (s : String) : List String :=
  match d.changed.find? (fun p => p.fst == s) with
  | some p => p.snd
  | none => base s

def parentsOf : List (String × String) → List String → List String
  | [], _ => []
  | e :: es, acc =>
    if acc.contains e.snd then e.fst :: parentsOf es acc else parentsOf es acc

def expand (deps : List (String × String)) (acc : List String) : List String :=
  acc ++ (parentsOf deps acc).filter (fun s => !acc.contains s)

def iterCone (deps : List (String × String)) (acc : List String) : Nat → List String
  | 0 => acc
  | n + 1 => expand deps (iterCone deps acc n)

def coneExec (d : ExecDelta) : List String :=
  iterCone d.deps (changedSymbols d) (d.deps.length + (changedSymbols d).length + 1)

def directDeps (deps : List (String × String)) (s : String) : List String :=
  (deps.filter (fun e => e.fst == s)).map Prod.snd

def reachable (deps : List (String × String)) (beh : String → List String)
    (s : String) : Nat → List String
  | 0 => []
  | n + 1 =>
    beh s ++ List.flatMap (fun t => reachable deps beh t n) (directDeps deps s)

def reachedObs (deps : List (String × String)) (beh : String → List String) (s : String) : List String :=
  reachable deps beh s (deps.length + 1)

def isForbiddenHit (forb : List String) (beh : String → List String) (s : String) : Bool :=
  forb.contains s && !(beh s).isEmpty

def isUnsafeObs (allow : String → List String) (beh : String → List String)
    (symHigh obsHigh : String → Bool) (deps : List (String × String)) (s : String) : Bool :=
  let got := reachedObs deps beh s
  got.any (fun o => !(allow s).contains o) || (!symHigh s && got.any obsHigh)

def changedCost (d : ExecDelta) : Nat :=
  d.changed.foldl (fun n p => n + p.snd.length) 0

def paretoOK (d : ExecDelta) : Bool :=
  decide (changedCost d ≤ d.boundTime) && decide (changedCost d ≤ d.boundCompute)

def scopeMiss (d : ExecDelta) : Option String :=
  (coneExec d).find? (fun s => !d.inspect.contains s)

def scopeForbidden (forb : List String) (base : String → List String) (d : ExecDelta) : Option String :=
  (coneExec d).find? (fun s => isForbiddenHit forb (behaviorAfter base d) s)

def scopeUnsafe (allow base : String → List String) (d : ExecDelta) : Option String :=
  (coneExec d).find? (fun s =>
    isUnsafeObs allow (behaviorAfter base d) d.symHigh d.obsHigh d.deps s)

def check (forb : List String) (allow base : String → List String) (d : ExecDelta) : Verdict String :=
  match scopeMiss d with
  | some s => .refuse s
  | none =>
    match scopeForbidden forb base d with
    | some s => .refuse s
    | none =>
      match scopeUnsafe allow base d with
      | some s => .refuse s
      | none =>
        if paretoOK d then
          .accept
        else
          match changedSymbols d with
          | s :: _ => .refuse s
          | [] => .accept

theorem not_isEmpty_iff {α : Type} (l : List α) : (!l.isEmpty) = true ↔ l ≠ [] := by
  cases l <;> simp [List.isEmpty]

theorem bool_not_true_iff_false (b : Bool) : (!b) = true ↔ b = false := by
  cases b <;> simp

theorem isForbiddenHit_iff (forb : List String) (beh : String → List String) (s : String) :
    isForbiddenHit forb beh s = true ↔ s ∈ forb ∧ beh s ≠ [] := by
  simp [isForbiddenHit, Bool.and_eq_true, List.contains_iff, not_isEmpty_iff]

theorem changedCost_of_nil {d : ExecDelta} (h : d.changed = []) : changedCost d = 0 := by
  simp [changedCost, h]

theorem changedSymbols_nil {d : ExecDelta} (h : changedSymbols d = []) : d.changed = [] := by
  cases hchg : d.changed with
  | nil => rfl
  | cons _ _ => simp [changedSymbols, hchg] at h

theorem paretoOK_zero {d : ExecDelta} (h : changedCost d = 0) : paretoOK d = true := by
  simp [paretoOK, h, decide_eq_true_iff, Nat.zero_le]

theorem paretoOK_iff (d : ExecDelta) :
    paretoOK d = true ↔
      paretoLE ⟨changedCost d, changedCost d⟩ ⟨d.boundTime, d.boundCompute⟩ := by
  simp [paretoOK, paretoLE, Bool.and_eq_true, decide_eq_true_iff]

theorem find?_none_iff {α : Type} {p : α → Bool} {l : List α} :
    l.find? p = none ↔ ∀ a, a ∈ l → p a = false := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    cases hp : p x with
    | true =>
      constructor
      · intro h
        simp [List.find?, hp] at h
      · intro h
        have hx := h x (List.Mem.head _)
        rw [hp] at hx
        cases hx
    | false =>
      simp [List.find?, hp, ih]

theorem check_accept_iff (forb : List String) (allow base : String → List String) (d : ExecDelta) :
    check forb allow base d = Verdict.accept ↔
      scopeMiss d = none ∧
      scopeForbidden forb base d = none ∧
      scopeUnsafe allow base d = none ∧
      paretoOK d = true := by
  cases hmiss : scopeMiss d with
  | some _ =>
    simp [check, hmiss]
  | none =>
    cases hforb : scopeForbidden forb base d with
    | some _ =>
      simp [check, hmiss, hforb]
    | none =>
      cases hunsafe : scopeUnsafe allow base d with
      | some _ =>
        simp [check, hmiss, hforb, hunsafe]
      | none =>
        cases hp : paretoOK d with
        | true =>
          simp [check, hmiss, hforb, hunsafe, hp]
        | false =>
          cases hc : changedSymbols d with
          | nil =>
            have hok : paretoOK d = true :=
              paretoOK_zero (changedCost_of_nil (changedSymbols_nil hc))
            rw [hp] at hok
            cases hok
          | cons _ _ =>
            simp [check, hmiss, hforb, hunsafe, hp, hc]

theorem check_refuse_iff (forb : List String) (allow base : String → List String)
    (d : ExecDelta) (name : String) :
    check forb allow base d = Verdict.refuse name ↔
      scopeMiss d = some name ∨
      (scopeMiss d = none ∧ scopeForbidden forb base d = some name) ∨
      (scopeMiss d = none ∧ scopeForbidden forb base d = none ∧
        scopeUnsafe allow base d = some name) ∨
      (scopeMiss d = none ∧ scopeForbidden forb base d = none ∧
        scopeUnsafe allow base d = none ∧ paretoOK d = false ∧
        (changedSymbols d).head? = some name) := by
  cases hmiss : scopeMiss d with
  | some _ =>
    simp [check, hmiss]
  | none =>
    cases hforb : scopeForbidden forb base d with
    | some _ =>
      simp [check, hmiss, hforb]
    | none =>
      cases hunsafe : scopeUnsafe allow base d with
      | some _ =>
        simp [check, hmiss, hforb, hunsafe]
      | none =>
        cases hp : paretoOK d with
        | true =>
          simp [check, hmiss, hforb, hunsafe, hp]
        | false =>
          cases hc : changedSymbols d with
          | nil =>
            have hok : paretoOK d = true :=
              paretoOK_zero (changedCost_of_nil (changedSymbols_nil hc))
            rw [hp] at hok
            cases hok
          | cons _ _ =>
            simp [check, hmiss, hforb, hunsafe, hp, hc, List.head?]

theorem forbidden_refusal_names (forb : List String) (allow base : String → List String)
    (d : ExecDelta) (name : String)
    (hmiss : scopeMiss d = none)
    (hforb : scopeForbidden forb base d = some name) :
    check forb allow base d = Verdict.refuse name ∧
      name ∈ forb ∧ behaviorAfter base d name ≠ [] ∧
      ∃ pre post, coneExec d = pre ++ name :: post ∧
        ∀ t, t ∈ pre → isForbiddenHit forb (behaviorAfter base d) t = false := by
  have hcheck := (check_refuse_iff forb allow base d name).mpr (Or.inr (Or.inl ⟨hmiss, hforb⟩))
  rcases List.find?_eq_some_iff_append.mp hforb with ⟨hhit, pre, post, hsplit, hpre⟩
  have hmem := (isForbiddenHit_iff forb (behaviorAfter base d) name).mp hhit
  exact ⟨hcheck, hmem.1, hmem.2, pre, post, hsplit,
    fun t ht => (bool_not_true_iff_false _).mp (hpre t ht)⟩

theorem accept_imp_pareto (forb : List String) (allow base : String → List String) (d : ExecDelta)
    (h : check forb allow base d = Verdict.accept) :
    paretoLE ⟨changedCost d, changedCost d⟩ ⟨d.boundTime, d.boundCompute⟩ :=
  (paretoOK_iff d).mp ((check_accept_iff forb allow base d).mp h).2.2.2

theorem accept_imp_no_new_forbidden (forb : List String) (allow base : String → List String)
    (d : ExecDelta) (h : check forb allow base d = Verdict.accept) :
    ∀ s, s ∈ coneExec d → s ∈ forb → behaviorAfter base d s = [] := by
  intro s hs hmem
  have hnone := ((check_accept_iff forb allow base d).mp h).2.1
  have hfalse : isForbiddenHit forb (behaviorAfter base d) s = false :=
    (find?_none_iff.mp (by simpa [scopeForbidden] using hnone)) s hs
  cases hbeh : behaviorAfter base d s with
  | nil => rfl
  | cons _ _ =>
    have hhit : isForbiddenHit forb (behaviorAfter base d) s = true :=
      (isForbiddenHit_iff forb (behaviorAfter base d) s).mpr ⟨hmem, by simp [hbeh]⟩
    rw [hfalse] at hhit
    cases hhit

def depProp (deps : List (String × String)) : String → String → Prop :=
  fun s t => (s, t) ∈ deps

def changedProp (seeds : List String) : String → Bool :=
  fun s => seeds.contains s

theorem parents_mem {deps : List (String × String)} {acc : List String} {s : String}
    (h : s ∈ parentsOf deps acc) : ∃ t, (s, t) ∈ deps ∧ t ∈ acc := by
  induction deps with
  | nil =>
    cases h
  | cons e es ih =>
    cases e with
    | mk a b =>
      cases hcb : acc.contains b with
      | true =>
        have hmem : s ∈ a :: parentsOf es acc := by
          simpa only [parentsOf, hcb] using h
        cases hmem with
        | head =>
          exact ⟨b, List.Mem.head _, List.contains_iff.mp hcb⟩
        | tail _ hs =>
          rcases ih hs with ⟨t, hdep, ht⟩
          exact ⟨t, List.Mem.tail _ hdep, ht⟩
      | false =>
        have hs : s ∈ parentsOf es acc := by
          simpa only [parentsOf, hcb] using h
        rcases ih hs with ⟨t, hdep, ht⟩
        exact ⟨t, List.Mem.tail _ hdep, ht⟩

theorem expand_cone {deps : List (String × String)} {seeds acc : List String} {s : String}
    (hacc : ∀ x, x ∈ acc → Cone (depProp deps) (changedProp seeds) x)
    (h : s ∈ expand deps acc) :
    Cone (depProp deps) (changedProp seeds) s := by
  rw [expand, List.mem_append] at h
  cases h with
  | inl hs => exact hacc s hs
  | inr hs =>
    have hfil := List.mem_filter.mp hs
    rcases parents_mem hfil.1 with ⟨t, hdep, ht⟩
    exact Cone.step hdep (hacc t ht)

theorem iter_cone {deps : List (String × String)} {seeds : List String} (n : Nat) {s : String}
    (h : s ∈ iterCone deps seeds n) :
    Cone (depProp deps) (changedProp seeds) s := by
  induction n generalizing s with
  | zero =>
    simp [iterCone] at h
    exact Cone.root (List.contains_iff.mpr h)
  | succ n ih =>
    rw [iterCone] at h
    exact expand_cone (fun x hx => ih hx) h

theorem coneExec_sound (d : ExecDelta) {s : String} (h : s ∈ coneExec d) :
    Cone (depProp d.deps) (changedProp (changedSymbols d)) s :=
  iter_cone (d.deps.length + (changedSymbols d).length + 1) (by simpa [coneExec] using h)

theorem checker_scope_in_cone (forb : List String) (allow base : String → List String)
    (d : ExecDelta) (name : String)
    (h : check forb allow base d = Verdict.refuse name)
    (hmiss : scopeMiss d = none) :
    name ∈ coneExec d ∨ (changedSymbols d).head? = some name := by
  rcases (check_refuse_iff forb allow base d name).mp h with h | h | h | h
  · nomatch (hmiss.symm.trans h)
  · rcases (List.find?_eq_some_iff_append.mp h.2).2 with ⟨pre, post, hsplit, _⟩
    exact Or.inl (by simp [hsplit])
  · rcases (List.find?_eq_some_iff_append.mp h.2.2).2 with ⟨pre, post, hsplit, _⟩
    exact Or.inl (by simp [hsplit])
  · exact Or.inr h.2.2.2.2

end SoftwareIsIncrementallySafe
