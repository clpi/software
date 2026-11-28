import Core
import Ops

/-! # Witnessed saturation on the one graph

    What a bounded, witness-driven equality saturation can and
    cannot change about the canonical graph of `Core` and `Ops`.

    1. Soundness is exactly witness soundness. For a valid graph
       and any meaning of terms, every equivalence the graph
       states is true of that meaning if and only if every join
       entry of the log relates terms of equal meaning
       (`soundiff`). So a search strategy, however greedy or
       bounded, can make the graph wrong only by appending a
       wrong witness; its heuristics, beams, schedules and fuel
       never touch soundness.
    2. A run of joins, each on a witness of equal meaning, keeps
       the graph valid and sound (`joinsound`, `joinssound`), and
       grows it (Ops `joingrows`).
    3. Arrival order. Two valid graphs whose logs hold the same
       join entries up to membership state the same equivalences
       on distinct terms (`orderfree`). What a bounded search
       finds may depend on the order witnesses arrive; what the
       graph says, given the same witnesses, does not.
    4. Observer-applied terms. When every join entry relates two
       terms `o(a)` and `o(b)` with equal keys under observer `o`,
       every equivalence between observer-applied terms is a fact
       of one observer (`appliedsound`): no leak across observers.
    5. Self-funding fuel. Steps that each cost at least one unit,
       paid from an initial budget plus refunds capped in total,
       number at most the budget plus the cap (`fuelbound`).
    6. AC normalization. Reordering the operands of a sum never
       changes its value (`sumperm`), so a step that sorts the
       operands of an AC operator is a sound witness.
-/

variable {Sym : Type}

/-- Every join entry of a log relates terms of equal meaning. -/
def WitnessSound (kinds : Kinds Sym) (log : List (Entry Sym)) {K : Type}
    (m : Term Sym → K) : Prop :=
  ∀ entry ∈ log, entry.kind = kinds.join →
    ∀ a ∈ entry.terms, ∀ b ∈ entry.terms, m a = m b

/-- Every equivalence the graph states holds of a meaning. -/
def GraphSound (graph : Graph Sym) {K : Type} (m : Term Sym → K) : Prop :=
  ∀ left right, same graph left right → m left = m right

/-- A chain over a witness-sound log relates terms of equal
    meaning. -/
theorem chainsound (kinds : Kinds Sym) {log : List (Entry Sym)} {K : Type}
    {m : Term Sym → K} (hw : WitnessSound kinds log m) :
    ∀ {left right : Term Sym}, Chain kinds log left right → m left = m right := by
  intro left right h
  induction h with
  | step hstep =>
      obtain ⟨entry, hentry, hkind, hl, hr⟩ := hstep
      exact hw entry hentry hkind _ hl _ hr
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-- Soundness of a valid graph is exactly soundness of its
    join witnesses. -/
theorem soundiff (kinds : Kinds Sym) (graph : Graph Sym) (valid : Valid kinds graph)
    {K : Type} (m : Term Sym → K) :
    GraphSound graph m ↔ WitnessSound kinds graph.log m := by
  constructor
  · intro hs entry hentry hkind a ha b hb
    exact hs a b (valid.exacttwo a b (.step ⟨entry, hentry, hkind, ha, hb⟩))
  · intro hw left right h
    rcases valid.exactone left right h with heq | hchain
    · rw [heq]
    · exact chainsound kinds hw hchain

/-- Entries added by a join: two entries and one join entry. -/
theorem joinlog [DecidableEq Sym] (kinds : Kinds Sym) (graph : Graph Sym)
    (one two : Term Sym) (level wit : Sym) :
    (join kinds graph one two level wit).log =
      graph.log ++ [⟨kinds.enter, [one], level, wit⟩] ++
        [⟨kinds.enter, [two], level, wit⟩] ++ [⟨kinds.join, [one, two], level, wit⟩] := by
  simp only [join, mergelog, enterlog]

/-- A join on a witness of equal meaning keeps a valid, sound
    graph sound. -/
theorem joinsound [DecidableEq Sym] (kinds : Kinds Sym) (graph : Graph Sym)
    (valid : Valid kinds graph) {K : Type} (m : Term Sym → K)
    (hs : GraphSound graph m) (one two : Term Sym) (level wit : Sym)
    (hm : m one = m two) : GraphSound (join kinds graph one two level wit) m := by
  have hv := joinvalid kinds graph valid one two level wit
  rw [soundiff kinds _ hv]
  have hw := (soundiff kinds graph valid m).1 hs
  intro entry hentry hkind a ha b hb
  rw [joinlog] at hentry
  simp only [List.mem_append, List.mem_singleton] at hentry
  rcases hentry with ((hold | hent) | hent) | hent
  · exact hw entry hold hkind a ha b hb
  · subst hent
    exact absurd hkind kinds.distinct.1
  · subst hent
    exact absurd hkind kinds.distinct.1
  · subst hent
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · rfl
    · exact hm
    · exact hm.symm
    · rfl

/-- A list of joins, each on a witness of equal meaning. -/
def witjoins [DecidableEq Sym] (kinds : Kinds Sym) (graph : Graph Sym) :
    List (Term Sym × Term Sym × Sym × Sym) → Graph Sym
  | [] => graph
  | (a, b, l, w) :: rest => witjoins kinds (join kinds graph a b l w) rest

/-- Any run of witnessed joins from a valid sound graph ends
    valid and sound. A search's heuristics choose the list; they
    cannot make the result unsound. -/
theorem joinssound [DecidableEq Sym] (kinds : Kinds Sym) {K : Type} (m : Term Sym → K) :
    ∀ (ops : List (Term Sym × Term Sym × Sym × Sym)) (graph : Graph Sym),
      Valid kinds graph → GraphSound graph m →
      (∀ op ∈ ops, m op.1 = m op.2.1) →
      Valid kinds (witjoins kinds graph ops) ∧ GraphSound (witjoins kinds graph ops) m := by
  intro ops
  induction ops with
  | nil => intro graph hv hs _; exact ⟨hv, hs⟩
  | cons op rest ih =>
    intro graph hv hs hops
    obtain ⟨a, b, l, w⟩ := op
    have hab : m a = m b := hops (a, b, l, w) (List.mem_cons_self)
    exact ih (join kinds graph a b l w) (joinvalid kinds graph hv a b l w)
      (joinsound kinds graph hv m hs a b l w hab)
      (fun op hop => hops op (List.mem_cons_of_mem _ hop))

/-- The empty graph is sound for every meaning. -/
theorem emptysound {K : Type} (m : Term Sym → K) : GraphSound (empty : Graph Sym) m := by
  intro left right h
  obtain ⟨edge, hedge, _⟩ := h
  cases hedge

/-- A chain depends on the log only through its join entries. -/
theorem chainof (kinds : Kinds Sym) {log log' : List (Entry Sym)}
    (hsub : ∀ entry, entry ∈ log → entry.kind = kinds.join → entry ∈ log') :
    ∀ {left right : Term Sym}, Chain kinds log left right → Chain kinds log' left right := by
  intro left right h
  induction h with
  | step hstep =>
      obtain ⟨entry, hentry, hkind, hl, hr⟩ := hstep
      exact .step ⟨entry, hsub entry hentry hkind, hkind, hl, hr⟩
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2

/-- Arrival order does not change what the graph states: two
    valid graphs with the same join entries, up to membership,
    state the same equivalences between distinct terms. -/
theorem orderfree (kinds : Kinds Sym) (g h : Graph Sym)
    (vg : Valid kinds g) (vh : Valid kinds h)
    (hjoins : ∀ entry, entry.kind = kinds.join → (entry ∈ g.log ↔ entry ∈ h.log))
    (left right : Term Sym) (hne : left ≠ right) :
    same g left right ↔ same h left right := by
  constructor
  · intro hs
    rcases vg.exactone left right hs with heq | hc
    · exact absurd heq hne
    · exact vh.exacttwo left right
        (chainof kinds (fun e he hk => (hjoins e hk).1 he) hc)
  · intro hs
    rcases vh.exactone left right hs with heq | hc
    · exact absurd heq hne
    · exact vg.exacttwo left right
        (chainof kinds (fun e he hk => (hjoins e hk).2 he) hc)

/-- The observer-applied term `o(t)`: a form whose head is the
    observer's symbol and whose one argument is the term. -/
def applied (o : Sym) (t : Term Sym) : Term Sym := .form (.atom o) [t]

/-- The meaning of an observer-applied term: its observer and
    the observer's key of its argument. Other terms mean
    nothing. -/
def qmean {K : Type} (key : Sym → Term Sym → K) : Term Sym → Option (Sym × K)
  | .form (.atom o) [t] => some (o, key o t)
  | _ => none

theorem qmeanapplied {K : Type} (key : Sym → Term Sym → K) (o : Sym) (t : Term Sym) :
    qmean key (applied o t) = some (o, key o t) := rfl

/-- When every join entry relates `o(a)` and `o(b)` with equal
    keys under `o`, every equivalence between observer-applied
    terms is a fact of one observer: no leak across observers. -/
theorem appliedsound (kinds : Kinds Sym) (graph : Graph Sym) (valid : Valid kinds graph)
    {K : Type} (key : Sym → Term Sym → K)
    (hlog : ∀ entry ∈ graph.log, entry.kind = kinds.join →
      ∃ o a b, entry.terms = [applied o a, applied o b] ∧ key o a = key o b)
    (o o' : Sym) (a b : Term Sym) (hs : same graph (applied o a) (applied o' b)) :
    o = o' ∧ key o a = key o' b := by
  have hw : WitnessSound kinds graph.log (qmean key) := by
    intro entry hentry hkind x hx y hy
    obtain ⟨p, c, d, hterms, hkey⟩ := hlog entry hentry hkind
    rw [hterms] at hx hy
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
      simp only [qmeanapplied, hkey]
  have := (soundiff kinds graph valid (qmean key)).2 hw _ _ hs
  simp only [qmeanapplied, Option.some.injEq, Prod.mk.injEq] at this
  obtain ⟨h1, h2⟩ := this
  subst h1
  exact ⟨rfl, h2⟩

/-- Length is at most sum when every element is at least one. -/
theorem lenle : ∀ (costs : List Nat), (∀ c ∈ costs, 1 ≤ c) → costs.length ≤ costs.sum := by
  intro costs
  induction costs with
  | nil => intro _; simp
  | cons c rest ih =>
    intro h
    have hc := h c (List.mem_cons_self)
    have hr := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp only [List.length_cons, List.sum_cons]
    omega

/-- Self-funding fuel terminates: steps that each cost at least
    one unit, paid from a budget `b0` plus refunds whose total is
    capped by `cap`, number at most `b0 + cap`. -/
theorem fuelbound (b0 cap : Nat) (costs refunds : List Nat)
    (hcost : ∀ c ∈ costs, 1 ≤ c) (hcap : refunds.sum ≤ cap)
    (hsolvent : costs.sum ≤ b0 + refunds.sum) : costs.length ≤ b0 + cap := by
  have := lenle costs hcost
  omega

/-- The value of a sum. -/
def sumof : List Int → Int
  | [] => 0
  | x :: rest => x + sumof rest

/-- Reordering operands never changes a sum: sorting the
    operands of an AC operator is a sound witness. -/
theorem sumperm {l l' : List Int} (h : l.Perm l') : sumof l = sumof l' := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp only [sumof, ih]
  | swap x y rest => simp only [sumof]; omega
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

#print axioms chainsound
#print axioms soundiff
#print axioms joinlog
#print axioms joinsound
#print axioms joinssound
#print axioms emptysound
#print axioms chainof
#print axioms orderfree
#print axioms qmeanapplied
#print axioms appliedsound
#print axioms lenle
#print axioms fuelbound
#print axioms sumperm

/- ## Inside the bound -/

/-- Exactness at a resolution. When the run has joined `o(a)` with
    `o(b)` for every pair whose keys agree (and only such pairs), two
    observer-applied terms stand together exactly when their keys
    agree. With the key "values on every resolved point", exhaustive
    evaluation decides the bounded join: sound and complete inside the
    bound. -/
theorem boundedexact (kinds : Kinds Sym) (graph : Graph Sym) (valid : Valid kinds graph)
    {K : Type} (key : Sym → Term Sym → K)
    (honly : ∀ entry ∈ graph.log, entry.kind = kinds.join →
      ∃ o a b, entry.terms = [applied o a, applied o b] ∧ key o a = key o b)
    (hall : ∀ o a b, key o a = key o b →
      ∃ entry ∈ graph.log, entry.kind = kinds.join ∧
        applied o a ∈ entry.terms ∧ applied o b ∈ entry.terms)
    (o : Sym) (a b : Term Sym) :
    same graph (applied o a) (applied o b) ↔ key o a = key o b := by
  constructor
  · intro hs
    exact (appliedsound kinds graph valid key honly o o a b hs).2
  · intro hk
    obtain ⟨entry, hentry, hkind, ha, hb⟩ := hall o a b hk
    exact valid.exacttwo _ _ (.step ⟨entry, hentry, hkind, ha, hb⟩)

/-- Saturation to the bound is maximal: if every join entry of a
    search's graph relates terms that already stand together in a
    saturated graph (the search used rule instances the saturated graph
    contains), every equivalence the search states between distinct
    terms stands in the saturated graph. No search over the same rule
    instances finds a join that saturation to the bound misses. -/
theorem saturationmax (kinds : Kinds Sym) (g h : Graph Sym) (vg : Valid kinds g)
    (hinst : ∀ entry ∈ h.log, entry.kind = kinds.join →
      ∀ a ∈ entry.terms, ∀ b ∈ entry.terms, a = b ∨ same g a b)
    (left right : Term Sym) (vh : Valid kinds h) (hne : left ≠ right)
    (hs : same h left right) : same g left right := by
  have key : ∀ {x y : Term Sym}, Chain kinds h.log x y → x = y ∨ same g x y := by
    intro x y hc
    induction hc with
    | step hstep =>
        obtain ⟨entry, hentry, hkind, hx, hy⟩ := hstep
        exact hinst entry hentry hkind _ hx _ hy
    | trans _ _ ih1 ih2 =>
        rcases ih1 with rfl | h1
        · exact ih2
        · rcases ih2 with rfl | h2
          · exact Or.inr h1
          · exact Or.inr (sametrans kinds g vg h1 h2)
  rcases vh.exactone left right hs with heq | hc
  · exact absurd heq hne
  · rcases key hc with heq | hsg
    · exact absurd heq hne
    · exact hsg

#print axioms boundedexact
#print axioms saturationmax

/-! ## The bounded decider covers every sound engine

The decider joins `o(a)` and `o(b)` exactly when the observer's key
agrees (`boundedexact`). Any other engine whose graph is sound for a
meaning that the key reads cannot state a join the decider lacks:
neither a join of observed terms nor a join of raw terms. So inside
the bound no sound procedure finds a join the decider misses. -/

/-- Joins of observed terms: whatever a sound engine joins at an
    observer, the decider joins too. -/
theorem decidermax (kinds : Kinds Sym) (g h : Graph Sym) (vg : Valid kinds g)
    {K M : Type} (key : Sym → Term Sym → K) (m : Term Sym → M)
    (honly : ∀ entry ∈ g.log, entry.kind = kinds.join →
      ∃ o a b, entry.terms = [applied o a, applied o b] ∧ key o a = key o b)
    (hall : ∀ o a b, key o a = key o b →
      ∃ entry ∈ g.log, entry.kind = kinds.join ∧
        applied o a ∈ entry.terms ∧ applied o b ∈ entry.terms)
    (hsound : GraphSound h m)
    (hreads : ∀ o a b, m (applied o a) = m (applied o b) → key o a = key o b)
    (o : Sym) (a b : Term Sym) (hs : same h (applied o a) (applied o b)) :
    same g (applied o a) (applied o b) :=
  (boundedexact kinds g vg key honly hall o a b).2 (hreads o a b (hsound _ _ hs))

/-- Joins of raw terms: a rewriting engine that joins `a` and `b`
    soundly gives a join the decider already holds at every
    observer that reads the meaning. -/
theorem decidercovers (kinds : Kinds Sym) (g h : Graph Sym) (vg : Valid kinds g)
    {K M : Type} (key : Sym → Term Sym → K) (m : Term Sym → M)
    (honly : ∀ entry ∈ g.log, entry.kind = kinds.join →
      ∃ o a b, entry.terms = [applied o a, applied o b] ∧ key o a = key o b)
    (hall : ∀ o a b, key o a = key o b →
      ∃ entry ∈ g.log, entry.kind = kinds.join ∧
        applied o a ∈ entry.terms ∧ applied o b ∈ entry.terms)
    (hsound : GraphSound h m)
    (hreads : ∀ o a b, m a = m b → key o a = key o b)
    (a b : Term Sym) (hs : same h a b) (o : Sym) :
    same g (applied o a) (applied o b) :=
  (boundedexact kinds g vg key honly hall o a b).2 (hreads o a b (hsound _ _ hs))

#print axioms decidermax
#print axioms decidercovers
