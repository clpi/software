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

inductive NodeKind where
  | code
  | context
  | configuration
  | data
  deriving DecidableEq, Repr, BEq

structure RepoSpec where
  deps : List (String × String)
  allow : String → List String
  symHigh : String → Bool
  obsHigh : String → Bool
  boundTime : Nat
  boundCompute : Nat
  required : String → List String
  obsCost : String → Nat
  forbidden : List String
  kind : String → NodeKind

def coneExecOf (deps : List (String × String)) (seeds : List String) : List String :=
  iterCone deps seeds (deps.length + seeds.length + 1)

def specCone (spec : RepoSpec) (d : ExecDelta) : List String :=
  coneExecOf spec.deps (changedSymbols d)

def directDeps (deps : List (String × String)) (s : String) : List String :=
  (deps.filter (fun e => e.fst == s)).map Prod.snd

def reachFuel (deps : List (String × String)) : Nat :=
  (deps.length + 1) * (deps.length + 2)

def collect (deps : List (String × String)) (beh : String → List String)
    (todo seen : List String) : Nat → List String
  | 0 => []
  | n + 1 =>
    match todo with
    | [] => []
    | s :: rest =>
      if seen.contains s then
        collect deps beh rest seen n
      else
        beh s ++ collect deps beh (directDeps deps s ++ rest) (s :: seen) n

def reachedObs (deps : List (String × String)) (beh : String → List String) (s : String) : List String :=
  collect deps beh [s] [] (reachFuel deps)

def cycleDeps : List (String × String) :=
  [("a", "b"), ("b", "c"), ("c", "a"), ("a", "c"), ("b", "a"), ("c", "b")]

def cycleBeh : String → List String
  | "a" => ["oa"]
  | "b" => ["ob"]
  | "c" => ["oc"]
  | _ => ["other"]

theorem cycle_reached_once :
    reachedObs cycleDeps cycleBeh "a" = ["oa", "ob", "oc"] := by
  decide

def denseSyms : List String :=
  ["s0", "s1", "s2", "s3", "s4"]

def denseDeps : List (String × String) :=
  denseSyms.flatMap (fun a => denseSyms.map (fun b => (a, b)))

def denseBeh : String → List String
  | "s0" => ["o0"]
  | "s1" => ["o1"]
  | "s2" => ["o2"]
  | "s3" => ["o3"]
  | "s4" => ["o4"]
  | _ => []

theorem dense_reached_once :
    reachedObs denseDeps denseBeh "s0" = ["o0", "o1", "o2", "o3", "o4"] := by
  decide

def isForbiddenHit (forb : List String) (beh : String → List String) (s : String) : Bool :=
  forb.contains s && !(beh s).isEmpty

def isUnsafeObs (allow : String → List String) (beh : String → List String)
    (symHigh obsHigh : String → Bool) (deps : List (String × String)) (s : String) : Bool :=
  let got := reachedObs deps beh s
  got.any (fun o => !(allow s).contains o) || (!symHigh s && got.any obsHigh)

def changedCost (spec : RepoSpec) (d : ExecDelta) : Nat :=
  d.changed.foldl (fun n p => n + p.snd.foldl (fun m o => m + spec.obsCost o) 0) 0

def paretoOK (spec : RepoSpec) (d : ExecDelta) : Bool :=
  decide (changedCost spec d ≤ spec.boundTime) &&
    decide (changedCost spec d ≤ spec.boundCompute)

def missingRequired (spec : RepoSpec) (base : String → List String) (d : ExecDelta) (s : String) : Bool :=
  (spec.required s).any (fun o => !(behaviorAfter base d s).contains o)

def scopeRequired (spec : RepoSpec) (base : String → List String) (d : ExecDelta) : Option String :=
  (specCone spec d).find? (fun s => missingRequired spec base d s)

def scopeForbidden (spec : RepoSpec) (base : String → List String) (d : ExecDelta) : Option String :=
  (specCone spec d).find? (fun s => isForbiddenHit spec.forbidden (behaviorAfter base d) s)

def scopeUnsafe (spec : RepoSpec) (base : String → List String) (d : ExecDelta) : Option String :=
  (specCone spec d).find? (fun s =>
    isUnsafeObs spec.allow (behaviorAfter base d) spec.symHigh spec.obsHigh spec.deps s)

def check (spec : RepoSpec) (base : String → List String) (d : ExecDelta) : Verdict String :=
  match scopeRequired spec base d with
  | some s => .refuse s
  | none =>
    match scopeForbidden spec base d with
    | some s => .refuse s
    | none =>
      match scopeUnsafe spec base d with
      | some s => .refuse s
      | none =>
        if paretoOK spec d then
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

theorem changedCost_of_nil {spec : RepoSpec} {d : ExecDelta} (h : d.changed = []) :
    changedCost spec d = 0 := by
  simp [changedCost, h]

theorem changedSymbols_nil {d : ExecDelta} (h : changedSymbols d = []) : d.changed = [] := by
  cases hchg : d.changed with
  | nil => rfl
  | cons _ _ => simp [changedSymbols, hchg] at h

theorem paretoOK_zero {spec : RepoSpec} {d : ExecDelta} (h : changedCost spec d = 0) :
    paretoOK spec d = true := by
  simp [paretoOK, h, decide_eq_true_iff, Nat.zero_le]

theorem paretoOK_iff (spec : RepoSpec) (d : ExecDelta) :
    paretoOK spec d = true ↔
      paretoLE ⟨changedCost spec d, changedCost spec d⟩ ⟨spec.boundTime, spec.boundCompute⟩ := by
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

theorem check_accept_iff (spec : RepoSpec) (base : String → List String) (d : ExecDelta) :
    check spec base d = Verdict.accept ↔
      scopeRequired spec base d = none ∧
      scopeForbidden spec base d = none ∧
      scopeUnsafe spec base d = none ∧
      paretoOK spec d = true := by
  cases hreq : scopeRequired spec base d with
  | some _ =>
    simp [check, hreq]
  | none =>
    cases hforb : scopeForbidden spec base d with
    | some _ =>
      simp [check, hreq, hforb]
    | none =>
      cases hunsafe : scopeUnsafe spec base d with
      | some _ =>
        simp [check, hreq, hforb, hunsafe]
      | none =>
        cases hp : paretoOK spec d with
        | true =>
          simp [check, hreq, hforb, hunsafe, hp]
        | false =>
          cases hc : changedSymbols d with
          | nil =>
            have hok : paretoOK spec d = true :=
              paretoOK_zero (changedCost_of_nil (changedSymbols_nil hc))
            rw [hp] at hok
            cases hok
          | cons _ _ =>
            simp [check, hreq, hforb, hunsafe, hp, hc]

theorem check_refuse_iff (spec : RepoSpec) (base : String → List String)
    (d : ExecDelta) (name : String) :
    check spec base d = Verdict.refuse name ↔
      scopeRequired spec base d = some name ∨
      (scopeRequired spec base d = none ∧ scopeForbidden spec base d = some name) ∨
      (scopeRequired spec base d = none ∧ scopeForbidden spec base d = none ∧
        scopeUnsafe spec base d = some name) ∨
      (scopeRequired spec base d = none ∧ scopeForbidden spec base d = none ∧
        scopeUnsafe spec base d = none ∧ paretoOK spec d = false ∧
        (changedSymbols d).head? = some name) := by
  cases hreq : scopeRequired spec base d with
  | some _ =>
    simp [check, hreq]
  | none =>
    cases hforb : scopeForbidden spec base d with
    | some _ =>
      simp [check, hreq, hforb]
    | none =>
      cases hunsafe : scopeUnsafe spec base d with
      | some _ =>
        simp [check, hreq, hforb, hunsafe]
      | none =>
        cases hp : paretoOK spec d with
        | true =>
          simp [check, hreq, hforb, hunsafe, hp]
        | false =>
          cases hc : changedSymbols d with
          | nil =>
            have hok : paretoOK spec d = true :=
              paretoOK_zero (changedCost_of_nil (changedSymbols_nil hc))
            rw [hp] at hok
            cases hok
          | cons _ _ =>
            simp [check, hreq, hforb, hunsafe, hp, hc, List.head?]

theorem forbidden_refusal_names (spec : RepoSpec) (base : String → List String)
    (d : ExecDelta) (name : String)
    (hreq : scopeRequired spec base d = none)
    (hforb : scopeForbidden spec base d = some name) :
    check spec base d = Verdict.refuse name ∧
      name ∈ spec.forbidden ∧ behaviorAfter base d name ≠ [] ∧
      ∃ pre post, specCone spec d = pre ++ name :: post ∧
        ∀ t, t ∈ pre → isForbiddenHit spec.forbidden (behaviorAfter base d) t = false := by
  have hcheck := (check_refuse_iff spec base d name).mpr (Or.inr (Or.inl ⟨hreq, hforb⟩))
  rcases List.find?_eq_some_iff_append.mp hforb with ⟨hhit, pre, post, hsplit, hpre⟩
  have hmem := (isForbiddenHit_iff spec.forbidden (behaviorAfter base d) name).mp hhit
  exact ⟨hcheck, hmem.1, hmem.2, pre, post, hsplit,
    fun t ht => (bool_not_true_iff_false _).mp (hpre t ht)⟩

theorem accept_imp_pareto (spec : RepoSpec) (base : String → List String) (d : ExecDelta)
    (h : check spec base d = Verdict.accept) :
    paretoLE ⟨changedCost spec d, changedCost spec d⟩ ⟨spec.boundTime, spec.boundCompute⟩ :=
  (paretoOK_iff spec d).mp ((check_accept_iff spec base d).mp h).2.2.2

theorem accept_imp_no_new_forbidden (spec : RepoSpec) (base : String → List String)
    (d : ExecDelta) (h : check spec base d = Verdict.accept) :
    ∀ s, s ∈ specCone spec d → s ∈ spec.forbidden → behaviorAfter base d s = [] := by
  intro s hs hmem
  have hnone := ((check_accept_iff spec base d).mp h).2.1
  have hfalse : isForbiddenHit spec.forbidden (behaviorAfter base d) s = false :=
    (find?_none_iff.mp (by simpa [scopeForbidden] using hnone)) s hs
  cases hbeh : behaviorAfter base d s with
  | nil => rfl
  | cons _ _ =>
    have hhit : isForbiddenHit spec.forbidden (behaviorAfter base d) s = true :=
      (isForbiddenHit_iff spec.forbidden (behaviorAfter base d) s).mpr ⟨hmem, by simp [hbeh]⟩
    rw [hfalse] at hhit
    cases hhit

def depProp (deps : List (String × String)) : String → String → Prop :=
  fun s t => (s, t) ∈ deps

def behProfile (beh : String → List String) : String → Profile String :=
  fun s => ⟨fun o => o ∈ beh s⟩

inductive SymReach (deps : List (String × String)) : String → String → Prop where
  | refl {s : String} : SymReach deps s s
  | step {s t u : String} : (s, t) ∈ deps → SymReach deps t u → SymReach deps s u

theorem symReach_obs {deps : List (String × String)} {beh : String → List String}
    {s u o : String} (h : SymReach deps s u) (ho : o ∈ beh u) :
    Reaches (depProp deps) (behProfile beh) s o :=
  SymReach.rec
    (motive := fun s tgt _ => o ∈ beh tgt → Reaches (depProp deps) (behProfile beh) s o)
    (fun {tgt} (ho : o ∈ beh tgt) => Reaches.here (by simpa [behProfile] using ho))
    (fun {_ _ _} hdep _ ih ho => Reaches.step hdep (ih ho))
    h ho

theorem mem_directDeps {deps : List (String × String)} {s t : String} :
    t ∈ directDeps deps s ↔ (s, t) ∈ deps := by
  induction deps with
  | nil => simp [directDeps]
  | cons e es ih =>
    cases e with
    | mk a b =>
      cases hb : a == s with
      | true =>
        have hs : a = s := (beq_iff_eq).mp hb
        subst hs
        simp [directDeps, List.filter_cons, hb, List.mem_cons, ih]
      | false =>
        have hne : a ≠ s := by
          intro h
          have : (a == s) = true := (beq_iff_eq).mpr h
          rw [hb] at this
          cases this
        simp only [directDeps, List.filter_cons, hb]
        constructor
        · intro h
          exact List.Mem.tail _ (ih.mp h)
        · intro h
          cases h with
          | head => exact (hne rfl).elim
          | tail _ h => exact ih.mpr h

theorem collect_sym {deps : List (String × String)} {beh : String → List String}
    {o : String} :
    ∀ (fuel : Nat) (todo seen : List String),
      o ∈ collect deps beh todo seen fuel →
      ∃ u, o ∈ beh u ∧ ∃ t, t ∈ todo ∧ SymReach deps t u
  | 0, _, _, h => by simp [collect] at h
  | n + 1, [], _, h => by simp [collect] at h
  | n + 1, s :: rest, seen, h => by
    cases hseen : seen.contains s with
    | true =>
      have h' : o ∈ collect deps beh rest seen n := by
        simpa only [collect, hseen] using h
      rcases collect_sym n rest seen h' with ⟨u, hou, t, ht, hsym⟩
      exact ⟨u, hou, t, List.Mem.tail _ ht, hsym⟩
    | false =>
      have h' : o ∈ beh s ++ collect deps beh (directDeps deps s ++ rest) (s :: seen) n := by
        simpa only [collect, hseen] using h
      rw [List.mem_append] at h'
      cases h' with
      | inl ho =>
        exact ⟨s, ho, s, List.Mem.head _, SymReach.refl⟩
      | inr ho =>
        rcases collect_sym n (directDeps deps s ++ rest) (s :: seen) ho with ⟨u, hou, t, ht, hsym⟩
        rw [List.mem_append] at ht
        cases ht with
        | inl hdir =>
          exact ⟨u, hou, s, List.Mem.head _, SymReach.step (mem_directDeps.mp hdir) hsym⟩
        | inr hrest =>
          exact ⟨u, hou, t, List.Mem.tail _ hrest, hsym⟩

theorem reachedObs_imp_reaches {deps : List (String × String)} {beh : String → List String}
    {s o : String} (h : o ∈ reachedObs deps beh s) :
    Reaches (depProp deps) (behProfile beh) s o := by
  rcases collect_sym (reachFuel deps) [s] [] h with ⟨u, hou, t, ht, hsym⟩
  cases ht with
  | head =>
    exact symReach_obs hsym hou
  | tail _ hempty =>
    exact (List.not_mem_nil hempty).elim

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

theorem coneExec_sound (deps : List (String × String)) (seeds : List String) {s : String}
    (h : s ∈ coneExecOf deps seeds) :
    Cone (depProp deps) (changedProp seeds) s :=
  iter_cone (deps.length + seeds.length + 1) (by simpa [coneExecOf] using h)

theorem checker_scope_in_cone (spec : RepoSpec) (base : String → List String)
    (d : ExecDelta) (name : String)
    (h : check spec base d = Verdict.refuse name)
    (hreq : scopeRequired spec base d = none) :
    name ∈ specCone spec d ∨ (changedSymbols d).head? = some name := by
  rcases (check_refuse_iff spec base d name).mp h with h | h | h | h
  · nomatch (hreq.symm.trans h)
  · rcases (List.find?_eq_some_iff_append.mp h.2).2 with ⟨pre, post, hsplit, _⟩
    exact Or.inl (by simp [hsplit])
  · rcases (List.find?_eq_some_iff_append.mp h.2.2).2 with ⟨pre, post, hsplit, _⟩
    exact Or.inl (by simp [hsplit])
  · exact Or.inr h.2.2.2.2

end SoftwareIsIncrementallySafe
