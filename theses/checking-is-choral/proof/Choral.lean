/-
  Choral checking: a development checked cone by cone, with the
  verdicts joined, accepts exactly what the whole check accepts.

  The model. A development is a finite set of modules over a type
  `M`. Each module has a own check outcome `own m` (its own file
  elaborates, given its dependencies' checked artifacts) and a
  dependency list `deps m`. A rank function with `rank d < rank m`
  for every dependency `d` of `m` witnesses that the dependency
  graph is acyclic; the level assignment computed from the real
  import graph of a development is such a rank.

  The whole check evaluates every module from its dependencies
  upward. A cone check evaluates the modules of one cone the same
  way and reads every out-of-cone dependency from a boundary: the
  values the other cones produced. The theorems below state that
  when the boundary agrees with the whole check outside the cone
  (the join's contract: the exchanged artifacts are the other
  cones' actual outputs), the cone's values equal the whole
  check's values on the cone, and the joined verdict over a
  covering family of cones is the whole verdict, in both
  directions. The principle audit joins the same way: a module's audit
  depends only on the checking environment at the module and its
  dependencies, the cone environment agrees with the whole
  environment there, and the audit list of a concatenated module
  list is the concatenation of the audit lists.
-/

namespace Choral

variable {M : Type} [DecidableEq M]
variable (own : M → Bool) (deps : M → List M) (rank : M → Nat)

/-- Conjunction of a predicate over a list, by recursion on the list. -/
def allon : List M → (M → Bool) → Bool
  | [], _ => true
  | d :: ds, p => p d && allon ds p

omit [DecidableEq M] in
theorem allcongr {p q : M → Bool} {l : List M}
    (h : ∀ d ∈ l, p d = q d) : allon l p = allon l q := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      show (p x && allon xs p) = (q x && allon xs q)
      rw [h x (List.Mem.head xs),
        ih (fun d hd => h d (List.mem_cons_of_mem x hd))]

/-- Whole-check evaluation with fuel. Fuel above a module's rank
    never changes the value (lemma `fueleval`). -/
def eval : Nat → M → Bool
  | 0, _ => false
  | f + 1, m => own m && allon (deps m) (eval f)

omit [DecidableEq M] in
theorem fueleval (hrank : ∀ m d, d ∈ deps m → rank d < rank m) :
    ∀ (f : Nat), ∀ (g : Nat) (m : M),
      rank m < f → rank m < g → eval own deps f m = eval own deps g m := by
  intro f
  induction f with
  | zero => intro g m h1 _; exact absurd h1 (Nat.not_lt_zero _)
  | succ f ih =>
      intro g m h1 h2
      cases g with
      | zero => exact absurd h2 (Nat.not_lt_zero _)
      | succ g =>
          show (own m && allon (deps m) (eval own deps f))
              = (own m && allon (deps m) (eval own deps g))
          congr 1
          apply allcongr
          intro d hd
          have hr := hrank m d hd
          exact ih g d (Nat.lt_of_lt_of_le hr (Nat.le_of_lt_succ h1))
            (Nat.lt_of_lt_of_le hr (Nat.le_of_lt_succ h2))

/-- The whole check's verdict for one module. -/
def whole (m : M) : Bool := eval own deps (Nat.succ (rank m)) m

omit [DecidableEq M] in
theorem wholefold (hrank : ∀ m d, d ∈ deps m → rank d < rank m) (m : M) :
    whole own deps rank m
      = (own m && allon (deps m) (whole own deps rank)) := by
  show eval own deps (Nat.succ (rank m)) m
      = (own m && allon (deps m) (whole own deps rank))
  have step : eval own deps (Nat.succ (rank m)) m
      = (own m && allon (deps m) (eval own deps (rank m))) := rfl
  rw [step]
  congr 1
  apply allcongr
  intro d hd
  exact fueleval own deps rank hrank (rank m) (rank d + 1) d
    (hrank m d hd) (Nat.lt_succ_self _)

/-- Cone evaluation with fuel: inside the cone, evaluate as the
    whole check does; outside the cone, read the boundary value at
    any fuel, including zero. -/
def evalin (C : List M) (b : M → Bool) : Nat → M → Bool
  | 0, m => if m ∈ C then false else b m
  | f + 1, m => if m ∈ C then own m && allon (deps m) (evalin C b f) else b m

theorem outread (C : List M) (b : M → Bool) (f : Nat) {m : M} (h : m ∉ C) :
    evalin own deps C b f m = b m := by
  cases f with
  | zero => show (if m ∈ C then false else b m) = b m; rw [if_neg h]
  | succ f =>
      show (if m ∈ C then own m && allon (deps m) (evalin own deps C b f)
            else b m) = b m
      rw [if_neg h]

theorem fuelcone (hrank : ∀ m d, d ∈ deps m → rank d < rank m)
    (C : List M) (b : M → Bool) :
    ∀ (f : Nat), ∀ (g : Nat) (m : M), m ∈ C →
      rank m < f → rank m < g →
      evalin own deps C b f m = evalin own deps C b g m := by
  intro f
  induction f with
  | zero => intro g m _ h1 _; exact absurd h1 (Nat.not_lt_zero _)
  | succ f ih =>
      intro g m hm h1 h2
      cases g with
      | zero => exact absurd h2 (Nat.not_lt_zero _)
      | succ g =>
          show (if m ∈ C then own m && allon (deps m) (evalin own deps C b f)
                else b m)
              = (if m ∈ C then own m && allon (deps m) (evalin own deps C b g)
                else b m)
          rw [if_pos hm, if_pos hm]
          congr 1
          apply allcongr
          intro d hd
          have hr := hrank m d hd
          by_cases hdc : d ∈ C
          · exact ih g d hdc (Nat.lt_of_lt_of_le hr (Nat.le_of_lt_succ h1))
              (Nat.lt_of_lt_of_le hr (Nat.le_of_lt_succ h2))
          · rw [outread own deps C b f hdc, outread own deps C b g hdc]

/-- The cone check's verdict for one module of the cone. -/
def cone (C : List M) (b : M → Bool) (m : M) : Bool :=
  evalin own deps C b (Nat.succ (rank m)) m

/-- Pointwise agreement: with a boundary that agrees with the whole
    check outside the cone, every cone value equals the whole value. -/
theorem conepoint (hrank : ∀ m d, d ∈ deps m → rank d < rank m)
    (C : List M) (b : M → Bool)
    (hb : ∀ d, d ∉ C → b d = whole own deps rank d) :
    ∀ m ∈ C, cone own deps rank C b m = whole own deps rank m := by
  have aux : ∀ k m, rank m ≤ k → m ∈ C →
      cone own deps rank C b m = whole own deps rank m := by
    intro k
    induction k with
    | zero =>
        intro m hrk hm
        have hdeps : deps m = [] := by
          cases h : deps m with
          | nil => rfl
          | cons d ds =>
              have hd : d ∈ deps m := by
                rw [h]; exact List.Mem.head ds
              have := hrank m d hd
              omega
        show evalin own deps C b (Nat.succ (rank m)) m = whole own deps rank m
        rw [wholefold own deps rank hrank m, hdeps]
        show (if m ∈ C then own m && allon (deps m) (evalin own deps C b (rank m))
              else b m) = (own m && allon ([] : List M) (whole own deps rank))
        rw [if_pos hm, hdeps]
        rfl
    | succ k ih =>
        intro m hrk hm
        rw [wholefold own deps rank hrank m]
        show (if m ∈ C then own m && allon (deps m) (evalin own deps C b (rank m))
              else b m) = (own m && allon (deps m) (whole own deps rank))
        rw [if_pos hm]
        congr 1
        apply allcongr
        intro d hd
        have hrd := hrank m d hd
        by_cases hdc : d ∈ C
        · have e1 : evalin own deps C b (rank m) d
              = cone own deps rank C b d :=
            fuelcone own deps rank hrank C b (rank m) (rank d + 1) d hdc
              hrd (Nat.lt_succ_self _)
          rw [e1]
          exact ih d (by omega) hdc
        · rw [outread own deps C b (rank m) hdc]
          exact hb d hdc
  intro m hm
  exact aux (rank m) m (Nat.le_refl _) hm

/-- The joined verdict over a covering family of three cones is the
    whole verdict. Coverage is the only demand on the family: the
    verdict join needs no disjointness. Each cone's boundary must
    agree with the whole check outside that cone. -/
theorem joinediff (hrank : ∀ m d, d ∈ deps m → rank d < rank m)
    (C₁ C₂ C₃ : List M) (B : List M → M → Bool)
    (hcover : ∀ m, m ∈ C₁ ∨ m ∈ C₂ ∨ m ∈ C₃)
    (hb : ∀ C ∈ [C₁, C₂, C₃], ∀ d, d ∉ C → B C d = whole own deps rank d) :
    (∀ m, whole own deps rank m = true) ↔
    (∀ C ∈ [C₁, C₂, C₃], ∀ m ∈ C, cone own deps rank C (B C) m = true) := by
  constructor
  · intro hw C hC m hm
    have e := conepoint own deps rank hrank C (B C) (hb C hC) m hm
    rw [e, hw m]
  · intro hj m
    have key : ∀ (C : List M), C ∈ [C₁, C₂, C₃] → m ∈ C →
        whole own deps rank m = true := by
      intro C hC hm
      have e := conepoint own deps rank hrank C (B C) (hb C hC) m hm
      rw [← e]
      exact hj C hC m hm
    rcases hcover m with h | h | h
    · exact key C₁ (by simp) h
    · exact key C₂ (by simp) h
    · exact key C₃ (by simp) h

/-- The environment a cone's checker holds: cone values inside the
    cone, boundary values outside it. -/
def envof (C : List M) (b : M → Bool) (m : M) : Bool :=
  if m ∈ C then cone own deps rank C b m else b m

/-- A module's audit, computed from a checking environment, agrees
    between the cone environment and the whole environment whenever
    the audit reads the environment only at the module and its
    dependencies. -/
theorem auditpoint {A : Type} (auditOf : (M → Bool) → M → List A)
    (haudit : ∀ (e₁ e₂ : M → Bool) (m : M),
      (∀ d, d = m ∨ d ∈ deps m → e₁ d = e₂ d) → auditOf e₁ m = auditOf e₂ m)
    (hrank : ∀ m d, d ∈ deps m → rank d < rank m)
    (C : List M) (b : M → Bool)
    (hb : ∀ d, d ∉ C → b d = whole own deps rank d)
    {m : M} (hm : m ∈ C) :
    auditOf (envof own deps rank C b) m
      = auditOf (whole own deps rank) m := by
  apply haudit
  intro d hd
  have agree : ∀ x ∈ C, envof own deps rank C b x = whole own deps rank x := by
    intro x hx
    show (if x ∈ C then cone own deps rank C b x else b x)
        = whole own deps rank x
    rw [if_pos hx]
    exact conepoint own deps rank hrank C b hb x hx
  rcases hd with hdeq | hdm
  · have hm2 : d ∈ C := by rw [hdeq]; exact hm
    exact agree d hm2
  · by_cases hdc : d ∈ C
    · exact agree d hdc
    · show (if d ∈ C then cone own deps rank C b d else b d)
          = whole own deps rank d
      rw [if_neg hdc]
      exact hb d hdc

omit [DecidableEq M] in
theorem flatcongr {A : Type} {f g : M → List A} {l : List M}
    (h : ∀ m ∈ l, f m = g m) : l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      rw [List.flatMap_cons, List.flatMap_cons,
        h x (List.Mem.head xs),
        ih (fun m hm => h m (List.mem_cons_of_mem x hm))]

/-- The audit join: over a module list that is the concatenation of
    the three cones, the whole audit list is the concatenation of
    the three cone audit lists. -/
theorem auditjoin {A : Type} (auditOf : (M → Bool) → M → List A)
    (haudit : ∀ (e₁ e₂ : M → Bool) (m : M),
      (∀ d, d = m ∨ d ∈ deps m → e₁ d = e₂ d) → auditOf e₁ m = auditOf e₂ m)
    (hrank : ∀ m d, d ∈ deps m → rank d < rank m)
    (C₁ C₂ C₃ : List M) (B : List M → M → Bool)
    (hb : ∀ C ∈ [C₁, C₂, C₃], ∀ d, d ∉ C → B C d = whole own deps rank d)
    (order : List M) (horder : order = C₁ ++ C₂ ++ C₃) :
    order.flatMap (auditOf (whole own deps rank))
      = (C₁.flatMap (auditOf (envof own deps rank C₁ (B C₁))))
        ++ (C₂.flatMap (auditOf (envof own deps rank C₂ (B C₂))))
        ++ (C₃.flatMap (auditOf (envof own deps rank C₃ (B C₃)))) := by
  have e1 : C₁.flatMap (auditOf (whole own deps rank))
      = C₁.flatMap (auditOf (envof own deps rank C₁ (B C₁))) :=
    flatcongr (fun m hm =>
      (auditpoint own deps rank auditOf haudit hrank C₁ (B C₁) (hb C₁ (by simp)) hm).symm)
  have e2 : C₂.flatMap (auditOf (whole own deps rank))
      = C₂.flatMap (auditOf (envof own deps rank C₂ (B C₂))) :=
    flatcongr (fun m hm =>
      (auditpoint own deps rank auditOf haudit hrank C₂ (B C₂) (hb C₂ (by simp)) hm).symm)
  have e3 : C₃.flatMap (auditOf (whole own deps rank))
      = C₃.flatMap (auditOf (envof own deps rank C₃ (B C₃))) :=
    flatcongr (fun m hm =>
      (auditpoint own deps rank auditOf haudit hrank C₃ (B C₃) (hb C₃ (by simp)) hm).symm)
  subst horder
  rw [List.flatMap_append, List.flatMap_append, e1, e2, e3]

end Choral
