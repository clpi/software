/-
  Software persistence is minimal: the proved model.

  The model, from the directive of 2026-11-19. Persistent data
  is a list of stored facts together with a list of recorded
  hyperedges; a fact is derivable when it is stored or follows
  by one recorded edge from derivable premises. A computation
  whose conclusion is already derivable is redundant, and
  adjoining a derivable fact to the store changes the derivable
  set not at all. A qualification contract carries a finite
  choice alphabet and a list of cost axes; a representation of
  a datum is minimum when no candidate in the finite candidate
  list dominates it, and the fold choice procedure returns a
  minimum by construction. Domination of one part lifts to the
  whole with the other parts fixed, so a minimum of the whole
  has minimum parts. A version stays readable while each of
  its parts stays derivable from the store. Every verdict has
  a boolean checker, separate from any producer, and each
  checker is tied to its predicate by a soundness theorem.
  Every theorem below is proved in full.
-/

namespace Persistence

/-- Derivability of a fact from a store of base facts through
    a list of recorded hyperedges. An edge is a pair of a
    premise list and a conclusion. -/
inductive Deriv (edges : List (List Nat × Nat)) (base : List Nat) :
    Nat → Prop where
  | base {c : Nat} : c ∈ base → Deriv edges base c
  | step {ps : List Nat} {c : Nat} : (ps, c) ∈ edges →
      (∀ p ∈ ps, Deriv edges base p) → Deriv edges base c

/-- Step closure: a recorded edge whose premises are all
    derivable has a derivable conclusion. This is the step
    constructor read as a theorem, the form the redundancy
    criterion uses. -/
theorem stepclose {edges : List (List Nat × Nat)} {base : List Nat}
    {ps : List Nat} {c : Nat} (hedge : (ps, c) ∈ edges)
    (hps : ∀ p ∈ ps, Deriv edges base p) : Deriv edges base c :=
  Deriv.step hedge hps

/-- Derivability is monotone in the store: a larger store
    derives at least as much. -/
theorem monof {edges : List (List Nat × Nat)} {base base' : List Nat}
    (hsub : ∀ x ∈ base, x ∈ base') {c : Nat}
    (h : Deriv edges base c) : Deriv edges base' c := by
  induction h with
  | base hmem => exact Deriv.base (hsub _ hmem)
  | step hedge _ ih => exact Deriv.step hedge ih

/-- Derivability is monotone in the recorded edges: recording
    more edges derives at least as much. -/
theorem monoe {edges edges' : List (List Nat × Nat)}
    (hsub : ∀ e ∈ edges, e ∈ edges') {base : List Nat} {c : Nat}
    (h : Deriv edges base c) : Deriv edges' base c := by
  induction h with
  | base hmem => exact Deriv.base hmem
  | step hedge _ ih => exact Deriv.step (hsub _ hedge) ih

/-- Elimination: adjoining an already derivable fact to the
    store changes the derivable set not at all, in both
    directions. A redundant computation is exactly one whose
    conclusion can be adjoined and removed without effect. -/
theorem elim {edges : List (List Nat × Nat)} {base : List Nat}
    {c x : Nat} (hc : Deriv edges base c) :
    Deriv edges (c :: base) x ↔ Deriv edges base x := by
  constructor
  · intro h
    induction h with
    | base hmem =>
      cases List.mem_cons.mp hmem with
      | inl h => subst h; exact hc
      | inr h => exact Deriv.base h
    | step hedge _ ih => exact Deriv.step hedge ih
  · intro h
    exact monof (fun y hy => List.mem_cons_of_mem c hy) h

/-- Running a certificate: fold the listed edges in order,
    checking at each step that every premise is already in
    the accumulated store, and adjoining the conclusion.
    Returns success and the final store. -/
def runCert : List Nat → List (List Nat × Nat) → Bool × List Nat
  | base, [] => (true, base)
  | base, (ps, c) :: rest =>
    if ps.all (fun p => decide (p ∈ base)) then
      runCert (c :: base) rest
    else
      (false, base)

/-- The certificate checker: every listed edge is recorded,
    the run succeeds, and the target is in the final store.
    The checker is separate from any certificate producer. -/
def checkCert (edges : List (List Nat × Nat)) (base : List Nat)
    (target : Nat) (cert : List (List Nat × Nat)) : Bool :=
  cert.all (fun e => decide (e ∈ edges)) && (runCert base cert).1
    && decide (target ∈ (runCert base cert).2)

/-- Soundness of the run: a successful run of recorded edges
    leaves only derivable facts in its final store. Proved by
    induction on the certificate, closing through the
    elimination theorem at each step. -/
theorem runsound {edges : List (List Nat × Nat)} :
    ∀ (cert : List (List Nat × Nat)) (base : List Nat),
      (∀ e ∈ cert, e ∈ edges) → (runCert base cert).1 = true →
      ∀ t ∈ (runCert base cert).2, Deriv edges base t := by
  intro cert
  induction cert with
  | nil =>
    intro base _ _ t ht
    exact Deriv.base ht
  | cons e rest ih =>
    obtain ⟨ps, c⟩ := e
    intro base hedge h1 t ht
    have heedge : (ps, c) ∈ edges := hedge _ (by simp)
    have hrest : ∀ e ∈ rest, e ∈ edges :=
      fun e he => hedge e (List.mem_cons_of_mem _ he)
    by_cases hcond : ps.all (fun p => decide (p ∈ base)) = true
    · have hrun : runCert base ((ps, c) :: rest)
          = runCert (c :: base) rest := by simp [runCert, hcond]
      rw [hrun] at h1 ht
      have hps : ∀ p ∈ ps, p ∈ base := by
        intro p hp
        exact of_decide_eq_true ((List.all_eq_true.mp hcond) p hp)
      have hc : Deriv edges base c :=
        Deriv.step heedge (fun p hp => Deriv.base (hps p hp))
      exact (elim hc).mp (ih (c :: base) hrest h1 t ht)
    · have hrun : runCert base ((ps, c) :: rest)
          = (false, base) := by simp [runCert, hcond]
      rw [hrun] at h1
      simp at h1

/-- Monotonicity of the run: a successful run stays
    successful under a larger store, and its final store only
    grows. -/
theorem runmono :
    ∀ (cert : List (List Nat × Nat)) (base base' : List Nat),
      (∀ x ∈ base, x ∈ base') → (runCert base cert).1 = true →
      (runCert base' cert).1 = true
        ∧ ∀ t ∈ (runCert base cert).2, t ∈ (runCert base' cert).2 := by
  intro cert
  induction cert with
  | nil =>
    intro base base' hsub _
    exact ⟨rfl, fun t ht => hsub t ht⟩
  | cons e rest ih =>
    obtain ⟨ps, c⟩ := e
    intro base base' hsub h1
    by_cases hcond : ps.all (fun p => decide (p ∈ base)) = true
    · have hcond' : ps.all (fun p => decide (p ∈ base')) = true := by
        rw [List.all_eq_true] at hcond ⊢
        intro p hp
        have hb : p ∈ base := of_decide_eq_true (hcond p hp)
        have hm : p ∈ base' := hsub p hb
        simp [hm]
      have hrun : runCert base ((ps, c) :: rest)
          = runCert (c :: base) rest := by simp [runCert, hcond]
      have hrun' : runCert base' ((ps, c) :: rest)
          = runCert (c :: base') rest := by simp [runCert, hcond']
      rw [hrun] at h1
      rw [hrun, hrun']
      exact ih (c :: base) (c :: base')
        (fun x hx => by
          cases List.mem_cons.mp hx with
          | inl h => subst h; exact List.mem_cons_self
          | inr h => exact List.mem_cons_of_mem _ (hsub x h)) h1
    · have hrun : runCert base ((ps, c) :: rest)
          = (false, base) := by simp [runCert, hcond]
      rw [hrun] at h1
      simp at h1

/-- Certificate soundness: a certificate the checker accepts
    witnesses a genuine derivation of the target. -/
theorem certsound {edges : List (List Nat × Nat)} {base : List Nat}
    {t : Nat} {cert : List (List Nat × Nat)}
    (h : checkCert edges base t cert = true) : Deriv edges base t := by
  have h' : (cert.all (fun e => decide (e ∈ edges))
      && (runCert base cert).1
      && decide (t ∈ (runCert base cert).2)) = true := h
  obtain ⟨hab, hc⟩ := Bool.and_eq_true_iff.mp h'
  obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp hab
  have hedge : ∀ e ∈ cert, e ∈ edges :=
    fun e he => of_decide_eq_true ((List.all_eq_true.mp ha) e he)
  have ht : t ∈ (runCert base cert).2 := of_decide_eq_true hc
  exact runsound cert base hedge hb t ht

/-- Certificate monotonicity: a certificate the checker
    accepts stays accepted as the recorded edges and the
    store grow. Certificates name only their premise cone, so
    growth of the persistent data never invalidates them.
    This is the incremental core. -/
theorem certmono {edges edges' : List (List Nat × Nat)}
    {base base' : List Nat} {t : Nat}
    {cert : List (List Nat × Nat)}
    (h : checkCert edges base t cert = true)
    (he : ∀ e ∈ edges, e ∈ edges') (hb : ∀ x ∈ base, x ∈ base') :
    checkCert edges' base' t cert = true := by
  have h' : (cert.all (fun e => decide (e ∈ edges))
      && (runCert base cert).1
      && decide (t ∈ (runCert base cert).2)) = true := h
  obtain ⟨hab, hc⟩ := Bool.and_eq_true_iff.mp h'
  obtain ⟨ha, hb1⟩ := Bool.and_eq_true_iff.mp hab
  have hall : cert.all (fun e => decide (e ∈ edges')) = true := by
    rw [List.all_eq_true]
    intro e hec
    have hm : e ∈ edges' :=
      he e (of_decide_eq_true ((List.all_eq_true.mp ha) e hec))
    simp [hm]
  have ht : t ∈ (runCert base cert).2 := of_decide_eq_true hc
  obtain ⟨h1, hmem⟩ := runmono cert base base' hb hb1
  have ht' : t ∈ (runCert base' cert).2 := hmem t ht
  have hgoal : (cert.all (fun e => decide (e ∈ edges'))
      && (runCert base' cert).1
      && decide (t ∈ (runCert base' cert).2)) = true :=
    Bool.and_eq_true_iff.mpr
      ⟨Bool.and_eq_true_iff.mpr ⟨hall, h1⟩, by
        simp only [decide_eq_true_eq]; exact ht'⟩
  exact hgoal

/-- Certificate composition at the run level: when a first
    certificate runs successfully to a store, running the
    concatenation from the start is running the second
    certificate from that store. -/
theorem certcomp :
    ∀ (c1 c2 : List (List Nat × Nat)) (base d : List Nat),
      runCert base c1 = (true, d) →
      runCert base (c1 ++ c2) = runCert d c2 := by
  intro c1
  induction c1 with
  | nil =>
    intro c2 base d h
    have h2 : (true, base) = (true, d) := h
    have hbd : base = d := congrArg Prod.snd h2
    subst hbd
    rfl
  | cons e rest ih =>
    obtain ⟨ps, c⟩ := e
    intro c2 base d h
    by_cases hcond : ps.all (fun p => decide (p ∈ base)) = true
    · have hrun : runCert base ((ps, c) :: rest)
          = runCert (c :: base) rest := by simp [runCert, hcond]
      rw [hrun] at h
      have hrun2 : runCert base ((ps, c) :: (rest ++ c2))
          = runCert (c :: base) (rest ++ c2) := by
        simp [runCert, hcond]
      show runCert base ((ps, c) :: (rest ++ c2)) = runCert d c2
      rw [hrun2]
      exact ih c2 (c :: base) d h
    · have hrun : runCert base ((ps, c) :: rest)
          = (false, base) := by simp [runCert, hcond]
      rw [hrun] at h
      simp at h

/-- Certificate composition at the checker level: a checked
    certificate for the second leg, composed after a
    successful first run of recorded edges, checks as one
    certificate from the original store. -/
theorem certcompcheck {edges : List (List Nat × Nat)}
    {base d : List Nat} {t : Nat}
    {c1 c2 : List (List Nat × Nat)}
    (hrun : runCert base c1 = (true, d))
    (h1 : ∀ e ∈ c1, e ∈ edges)
    (h2 : checkCert edges d t c2 = true) :
    checkCert edges base t (c1 ++ c2) = true := by
  have h2' : (c2.all (fun e => decide (e ∈ edges))
      && (runCert d c2).1
      && decide (t ∈ (runCert d c2).2)) = true := h2
  obtain ⟨hab2, hc2⟩ := Bool.and_eq_true_iff.mp h2'
  obtain ⟨ha2, hb2⟩ := Bool.and_eq_true_iff.mp hab2
  have hall : (c1 ++ c2).all (fun e => decide (e ∈ edges))
      = true := by
    rw [List.all_append]
    apply Bool.and_eq_true_iff.mpr
    constructor
    · rw [List.all_eq_true]
      intro e he
      have hm : e ∈ edges := h1 e he
      simp [hm]
    · exact ha2
  have hrun2 : runCert base (c1 ++ c2) = runCert d c2 :=
    certcomp c1 c2 base d hrun
  have hgoal : ((c1 ++ c2).all (fun e => decide (e ∈ edges))
      && (runCert base (c1 ++ c2)).1
      && decide (t ∈ (runCert base (c1 ++ c2)).2)) = true := by
    rw [hrun2]
    exact Bool.and_eq_true_iff.mpr
      ⟨Bool.and_eq_true_iff.mpr ⟨hall, hb2⟩, hc2⟩
  exact hgoal

/-- The qualification contract: a finite choice alphabet and
    a list of cost axes. The candidate space and every
    finiteness fact are derived from the contract, never
    assumed. -/
structure Contract where
  ch : List Nat
  axes : List (Nat → Nat → Nat)

/-- All representations of a given length over a choice
    alphabet: every list of choice codes of that length. -/
def reps : List Nat → Nat → List (List Nat)
  | _, 0 => [[]]
  | ch, n + 1 =>
    (reps ch n).flatMap (fun r => ch.map (fun c => c :: r))

/-- The sum of a constant list is the length times the
    constant. -/
theorem sumconst : ∀ (l : List Nat) (k : Nat),
    (l.map (fun _ => k)).sum = l.length * k := by
  intro l
  induction l with
  | nil => intro k; simp
  | cons a rest ih =>
    intro k
    show k + (rest.map (fun _ => k)).sum = (rest.length + 1) * k
    rw [ih, Nat.succ_mul]
    exact Nat.add_comm _ _

/-- The sum over a list of a function constant on the list
    is the length times the constant. -/
theorem sumconstf (f : List Nat → Nat) (k : Nat) :
    ∀ (l : List (List Nat)), (∀ r ∈ l, f r = k) →
      (l.map f).sum = l.length * k := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons a l ih =>
    intro h
    have ha : f a = k := h a List.mem_cons_self
    have ih' : (l.map f).sum = l.length * k :=
      ih (fun r hr => h r (List.mem_cons_of_mem a hr))
    show f a + (l.map f).sum = (l.length + 1) * k
    rw [ha, ih', Nat.succ_mul, Nat.add_comm]

/-- Finiteness, derived: the candidate count is the alphabet
    size raised to the length, a computed power from the
    contract. -/
theorem finite (c : Contract) (n : Nat) :
    (reps c.ch n).length = c.ch.length ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [reps]
    rw [List.length_flatMap,
      sumconstf (fun r => (c.ch.map (fun x => x :: r)).length)
        c.ch.length (reps c.ch n) (fun r _ => List.length_map _),
      ih, Nat.pow_succ]

/-- The cost of a representation of a datum on one axis: the
    sum over the zipped pairs of the axis values. -/
def cost (axis : Nat → Nat → Nat) (d r : List Nat) : Nat :=
  ((d.zip r).map (fun p => axis p.1 p.2)).sum

/-- Cost is additive over append of data and representations,
    segment by segment, when the segment lengths agree. -/
theorem costadd (a : Nat → Nat → Nat) :
    ∀ (d1 r1 d2 r2 : List Nat), d1.length = r1.length →
      d2.length = r2.length →
      cost a (d1 ++ d2) (r1 ++ r2)
        = cost a d1 r1 + cost a d2 r2 := by
  intro d1
  induction d1 with
  | nil =>
    intro r1 d2 r2 h1 h2
    cases r1 with
    | nil =>
      show cost a d2 r2 = cost a [] [] + cost a d2 r2
      rw [show cost a ([] : List Nat) ([] : List Nat) = 0 from rfl,
        Nat.zero_add]
    | cons y r1' => exact Nat.noConfusion h1
  | cons x d1' ih =>
    intro r1 d2 r2 h1 h2
    cases r1 with
    | nil => exact Nat.noConfusion h1
    | cons y r1' =>
      have hlen : d1'.length = r1'.length := Nat.succ.inj h1
      have ih' := ih r1' d2 r2 hlen h2
      show a x y + cost a (d1' ++ d2) (r1' ++ r2)
        = (a x y + cost a d1' r1') + cost a d2 r2
      rw [ih']
      exact (Nat.add_assoc _ _ _).symm

/-- The boolean at-most check on every axis of a list. -/
def leAll (axes : List (Nat → Nat → Nat)) (d s r : List Nat) :
    Bool :=
  axes.all (fun a => decide (cost a d s ≤ cost a d r))

/-- The boolean domination check: at most on every axis and
    strictly under on at least one. -/
def domB (axes : List (Nat → Nat → Nat)) (d s r : List Nat) :
    Bool :=
  leAll axes d s r
    && axes.any (fun a => decide (cost a d s < cost a d r))

/-- Domination as a proposition: one representation dominates
    another when it is at most on every named axis and
    strictly under on at least one. -/
def Dominates (axes : List (Nat → Nat → Nat)) (d s r : List Nat) :
    Prop :=
  (∀ a ∈ axes, cost a d s ≤ cost a d r)
    ∧ (∃ a ∈ axes, cost a d s < cost a d r)

/-- The boolean domination check decides the domination
    proposition, in both directions. -/
theorem dombridge {axes : List (Nat → Nat → Nat)}
    {d s r : List Nat} :
    domB axes d s r = true ↔ Dominates axes d s r := by
  constructor
  · intro h
    have h' : (leAll axes d s r
        && axes.any (fun a => decide (cost a d s < cost a d r)))
        = true := h
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp h'
    have h1' : axes.all (fun a => decide (cost a d s ≤ cost a d r))
        = true := h1
    have h2' : axes.any (fun a => decide (cost a d s < cost a d r))
        = true := h2
    constructor
    · intro a ha
      exact of_decide_eq_true ((List.all_eq_true.mp h1') a ha)
    · obtain ⟨a, ha, hda⟩ := List.any_eq_true.mp h2'
      exact ⟨a, ha, of_decide_eq_true hda⟩
  · intro h
    have hgoal : (leAll axes d s r
        && axes.any (fun a => decide (cost a d s < cost a d r)))
        = true := by
      apply Bool.and_eq_true_iff.mpr
      constructor
      · show axes.all (fun a => decide (cost a d s ≤ cost a d r))
          = true
        rw [List.all_eq_true]
        intro a ha
        simp only [decide_eq_true_eq]
        exact h.1 a ha
      · rw [List.any_eq_true]
        obtain ⟨a, ha, hlt⟩ := h.2
        exact ⟨a, ha, by simp only [decide_eq_true_eq]; exact hlt⟩
    exact hgoal

/-- A representation is minimum for a datum in a candidate
    list when it is a candidate and no candidate dominates
    it. -/
def Minimal (axes : List (Nat → Nat → Nat)) (d : List Nat)
    (cands : List (List Nat)) (r : List Nat) : Prop :=
  r ∈ cands ∧ ∀ s ∈ cands, ¬ Dominates axes d s r

/-- The boolean minimality checker, separate from the choice
    procedure that produces candidates. -/
def minimalB (axes : List (Nat → Nat → Nat)) (d : List Nat)
    (cands : List (List Nat)) (r : List Nat) : Bool :=
  decide (r ∈ cands)
    && cands.all (fun s => !domB axes d s r)

/-- Minimality checker soundness: a representation the
    checker accepts is minimum. -/
theorem mincheck {axes : List (Nat → Nat → Nat)} {d : List Nat}
    {cands : List (List Nat)} {r : List Nat}
    (h : minimalB axes d cands r = true) :
    Minimal axes d cands r := by
  have h' : (decide (r ∈ cands)
      && cands.all (fun s => !domB axes d s r)) = true := h
  obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp h'
  refine ⟨of_decide_eq_true h1, ?_⟩
  intro s hs hdom
  have hall : (!domB axes d s r) = true :=
    (List.all_eq_true.mp h2) s hs
  rw [dombridge.mpr hdom] at hall
  simp at hall

/-- Domination is irreflexive: nothing dominates itself,
    because the strict axis would be strict against itself. -/
theorem domirr {axes : List (Nat → Nat → Nat)} {d r : List Nat} :
    ¬ Dominates axes d r r := by
  intro h
  obtain ⟨a, -, hlt⟩ := h.2
  exact Nat.lt_irrefl _ hlt

/-- Domination is transitive: the at-most parts compose on
    every axis, and the strict axis of the second domination
    stays strict through the at-most part of the first. -/
theorem nodom {axes : List (Nat → Nat → Nat)} {d : List Nat}
    {x m s : List Nat} (h1 : Dominates axes d x m)
    (h2 : Dominates axes d s x) : Dominates axes d s m := by
  constructor
  · intro a ha
    exact Nat.le_trans (h2.1 a ha) (h1.1 a ha)
  · obtain ⟨a, ha, hlt⟩ := h2.2
    exact ⟨a, ha, Nat.lt_of_lt_of_le hlt (h1.1 a ha)⟩

/-- One step of the choice fold: keep the challenger exactly
    when it dominates the current best. -/
def keep (axes : List (Nat → Nat → Nat)) (d : List Nat)
    (best next : List Nat) : List Nat :=
  if domB axes d next best then next else best

/-- The choice procedure: fold the candidate list keeping an
    undominated candidate, starting from the first. -/
def choose (axes : List (Nat → Nat → Nat)) (d : List Nat) :
    List (List Nat) → List Nat
  | [] => []
  | r :: rs => rs.foldl (keep axes d) r

/-- The fold invariant: the fold result is the start value or
    a member of the folded list; nothing among the start
    value and the folded list dominates it; and anything
    dominating it already dominated the start value, so a
    switch of the accumulator can be chased back through the
    domination it switched on. -/
theorem choosecore {axes : List (Nat → Nat → Nat)}
    {d : List Nat} :
    ∀ (l : List (List Nat)) (acc : List Nat),
      (l.foldl (keep axes d) acc = acc
        ∨ l.foldl (keep axes d) acc ∈ l)
      ∧ (∀ s, s = acc ∨ s ∈ l →
          ¬ Dominates axes d s (l.foldl (keep axes d) acc))
      ∧ (∀ s, Dominates axes d s (l.foldl (keep axes d) acc)
          → Dominates axes d s acc) := by
  intro l
  induction l with
  | nil =>
    intro acc
    refine ⟨Or.inl rfl, ?_, fun _ h => h⟩
    intro s hs hdom
    cases hs with
    | inl h => subst h; exact domirr hdom
    | inr h => simp at h
  | cons x l ih =>
    intro acc
    have hfold : (x :: l).foldl (keep axes d) acc
        = l.foldl (keep axes d) (keep axes d acc x) := rfl
    rw [hfold]
    by_cases hdom : domB axes d x acc = true
    · have hkeep : keep axes d acc x = x := by
        simp [keep, hdom]
      rw [hkeep]
      obtain ⟨hmem, hnd, hback⟩ := ih x
      have hxa : Dominates axes d x acc := dombridge.mp hdom
      refine ⟨?_, ?_, ?_⟩
      · cases hmem with
        | inl h =>
          exact Or.inr (by rw [h]; exact List.mem_cons_self)
        | inr h =>
          exact Or.inr (List.mem_cons_of_mem x h)
      · intro s hs hds
        cases hs with
        | inl h =>
          subst h
          exact domirr (nodom hxa (hback s hds))
        | inr h =>
          cases List.mem_cons.mp h with
          | inl h => subst h; exact hnd s (Or.inl rfl) hds
          | inr h => exact hnd s (Or.inr h) hds
      · intro s hds
        exact nodom hxa (hback s hds)
    · have hndom : ¬ Dominates axes d x acc :=
        fun hd => hdom (dombridge.mpr hd)
      have hkeep : keep axes d acc x = acc := by
        simp [keep, hdom]
      rw [hkeep]
      obtain ⟨hmem, hnd, hback⟩ := ih acc
      refine ⟨?_, ?_, ?_⟩
      · cases hmem with
        | inl h => exact Or.inl h
        | inr h => exact Or.inr (List.mem_cons_of_mem x h)
      · intro s hs hds
        cases hs with
        | inl h => exact hnd s (Or.inl h) hds
        | inr h =>
          cases List.mem_cons.mp h with
          | inl h =>
            subst h; exact hndom (hback s hds)
          | inr h => exact hnd s (Or.inr h) hds
      · intro s hds
        exact hback s hds

/-- The choice procedure returns a minimum: its output is a
    candidate, and no candidate dominates it. Minimum by
    construction, from the fold invariant. -/
theorem choosemin {axes : List (Nat → Nat → Nat)} {d : List Nat}
    {cands : List (List Nat)} (hne : cands ≠ []) :
    (choose axes d cands) ∈ cands
      ∧ Minimal axes d cands (choose axes d cands) := by
  cases cands with
  | nil => exact absurd rfl hne
  | cons r rs =>
    obtain ⟨hmem, hnd, -⟩ := choosecore rs r
    have hmem' : rs.foldl (keep axes d) r ∈ r :: rs := by
      cases hmem with
      | inl h =>
        rw [h]; exact List.mem_cons_self
      | inr h => exact List.mem_cons_of_mem r h
    refine ⟨hmem', hmem', ?_⟩
    intro s hs hds
    cases List.mem_cons.mp hs with
    | inl h => subst h; exact hnd s (Or.inl rfl) hds
    | inr h => exact hnd s (Or.inr h) hds

/-- Existence: every nonempty candidate list carries a
    minimum, namely the output of the choice procedure. -/
theorem existsmin {axes : List (Nat → Nat → Nat)} {d : List Nat}
    {cands : List (List Nat)} (hne : cands ≠ []) :
    ∃ r, Minimal axes d cands r :=
  ⟨choose axes d cands, (choosemin hne).2⟩

/-- Domination lifts from a part to the whole: with the
    middle and last segments held fixed at equal cost on
    every axis, a domination of the first segment is a
    domination of the composed datum, by cost additivity.
    The length conditions are the segment agreements cost
    additivity needs. -/
theorem domlift {axes : List (Nat → Nat → Nat)}
    {d1 di d2 s1 ri r2 r1 : List Nat}
    (h : Dominates axes d1 s1 r1)
    (hs : d1.length = s1.length) (hr : d1.length = r1.length)
    (hi : di.length = ri.length) (h2 : d2.length = r2.length) :
    Dominates axes (d1 ++ di ++ d2) (s1 ++ ri ++ r2)
      (r1 ++ ri ++ r2) := by
  have key : ∀ a : Nat → Nat → Nat,
      cost a (d1 ++ di ++ d2) (s1 ++ ri ++ r2)
        = (cost a d1 s1 + cost a di ri) + cost a d2 r2
      ∧ cost a (d1 ++ di ++ d2) (r1 ++ ri ++ r2)
        = (cost a d1 r1 + cost a di ri) + cost a d2 r2 := by
    intro a
    have hlen : (d1 ++ di).length = (s1 ++ ri).length := by
      rw [List.length_append, List.length_append, hs, hi]
    have hlen2 : (d1 ++ di).length = (r1 ++ ri).length := by
      rw [List.length_append, List.length_append, hr, hi]
    constructor
    · calc cost a (d1 ++ di ++ d2) (s1 ++ ri ++ r2)
          = cost a (d1 ++ di) (s1 ++ ri) + cost a d2 r2 :=
            costadd a (d1 ++ di) (s1 ++ ri) d2 r2 hlen h2
        _ = (cost a d1 s1 + cost a di ri) + cost a d2 r2 := by
            rw [costadd a d1 s1 di ri hs hi]
    · calc cost a (d1 ++ di ++ d2) (r1 ++ ri ++ r2)
          = cost a (d1 ++ di) (r1 ++ ri) + cost a d2 r2 :=
            costadd a (d1 ++ di) (r1 ++ ri) d2 r2 hlen2 h2
        _ = (cost a d1 r1 + cost a di ri) + cost a d2 r2 := by
            rw [costadd a d1 r1 di ri hr hi]
  constructor
  · intro a ha
    obtain ⟨e1, e2⟩ := key a
    rw [e1, e2]
    have hle := h.1 a ha
    exact Nat.add_le_add_right (Nat.add_le_add_right hle _) _
  · obtain ⟨a, ha, hlt⟩ := h.2
    obtain ⟨e1, e2⟩ := key a
    exact ⟨a, ha, by
      rw [e1, e2]
      exact Nat.add_lt_add_right (Nat.add_lt_add_right hlt _) _⟩

/-- A minimum of the whole has minimum parts: were some part
    representation to dominate the corresponding part of a
    whole minimum, the lift would dominate the whole,
    contradicting its minimality. The converse fails in
    general; the cross-part tradeoff control in the controls
    file is the standing witness. -/
theorem wholemin {axes : List (Nat → Nat → Nat)}
    {d1 di d2 ri r2 r1 : List Nat}
    {C c1 : List (List Nat)}
    (hm : Minimal axes (d1 ++ di ++ d2) C (r1 ++ ri ++ r2))
    (hr : d1.length = r1.length) (hi : di.length = ri.length)
    (h2 : d2.length = r2.length) :
    ∀ s1 ∈ c1, s1.length = d1.length →
      (s1 ++ ri ++ r2) ∈ C → ¬ Dominates axes d1 s1 r1 := by
  intro s1 _ hlen hmem hdom
  exact hm.2 _ hmem (domlift hdom hlen.symm hr hi h2)

/-- A version is readable from a store when every one of its
    parts is derivable from the stored facts through the
    recorded edges. Readability is the semi-persistence
    predicate: the version survives exactly while its parts
    stay in the closure. -/
def Readable (edges : List (List Nat × Nat)) (stored : List Nat)
    (v : List Nat) : Prop :=
  ∀ p ∈ v, Deriv edges stored p

/-- Readability is monotone in the store: growing the stored
    facts never loses a readable version. -/
theorem readmono {edges : List (List Nat × Nat)}
    {stored stored' : List Nat} {v : List Nat}
    (h : Readable edges stored v)
    (hsub : ∀ x ∈ stored, x ∈ stored') :
    Readable edges stored' v :=
  fun p hp => monof hsub (h p hp)

/-- The total cost of a list of versions under one axis: the
    sum over the zipped versions and representations of the
    per-version costs. -/
def vcost (axis : Nat → Nat → Nat) (vs rs : List (List Nat)) :
    Nat :=
  ((vs.zip rs).map (fun p => cost axis p.1 p.2)).sum

/-- The total version cost splits at the head: the first
    version cost plus the rest. -/
theorem vcostcons (a : Nat → Nat → Nat) (v : List Nat)
    (vs : List (List Nat)) (r : List Nat)
    (rs : List (List Nat)) :
    vcost a (v :: vs) (r :: rs) = cost a v r + vcost a vs rs :=
  rfl

/-- The kept-premise fact: with the shared premise stored,
    the version that derives through the recorded edge stays
    readable. Keeping the premise as a recorded interaction
    is what semi-persistence consists in here. -/
theorem kept : Readable [([10], 20)] [10] [20] := by
  intro p hp
  have hp20 : p = 20 := by simpa using hp
  subst hp20
  refine Deriv.step (show ([10], 20) ∈ [([10], 20)] by simp) ?_
  intro q hq
  have hq10 : q = 10 := by simpa using hq
  subst hq10
  exact Deriv.base (by simp)

#print axioms stepclose
#print axioms monof
#print axioms monoe
#print axioms elim
#print axioms runsound
#print axioms runmono
#print axioms certsound
#print axioms certmono
#print axioms certcomp
#print axioms certcompcheck
#print axioms sumconst
#print axioms sumconstf
#print axioms finite
#print axioms costadd
#print axioms dombridge
#print axioms mincheck
#print axioms domirr
#print axioms nodom
#print axioms choosecore
#print axioms choosemin
#print axioms existsmin
#print axioms domlift
#print axioms wholemin
#print axioms readmono
#print axioms vcostcons
#print axioms kept

end Persistence
