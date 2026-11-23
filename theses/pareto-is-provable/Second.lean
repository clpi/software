import Pareto

/- Pareto proof program, lane 2: obligations 10 to 13 and 15 to
   20 over the section 0 definitions of the methodology record
   of 2026-11-22, building on lane 1 at its pin. Premises P1 to
   P4 stay as lane 1 left them: named in the registry, in
   content where lane 1 put them, never discharged. Finiteness
   is derived, never a hypothesis: the completeness proof
   terminates on a count taken from the finite row list itself. -/

namespace core

/-- The computed frontier of a table: the rows no other row in
    the table dominates, read through the solver verdict of
    obligation 9. -/
def front (axes : List axis) (rows : List row) : List row :=
  rows.filter (fun r => ! rows.any (fun o => verdict axes o r))

theorem anyfalse {α : Type} (l : List α) (p : α → Bool) :
    l.any p = false ↔ ∀ o ∈ l, p o = false := by
  constructor
  · intro h o ho
    by_cases hp : p o = true
    · have h2 : l.any p = true := List.any_eq_true.mpr ⟨o, ho, hp⟩
      rw [h] at h2
      cases h2
    · cases hb : p o with
      | false => rfl
      | true => exact absurd hb hp
  · intro h
    cases ha : l.any p with
    | false => rfl
    | true =>
      obtain ⟨o, ho, hp⟩ := List.any_eq_true.mp ha
      rw [h o ho] at hp
      cases hp

theorem anyeq {α : Type} (l : List α) (p q : α → Bool)
    (h : ∀ o ∈ l, p o = q o) : l.any p = l.any q := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.any_cons]
    rw [h a (List.Mem.head rest),
      ih (fun o ho => h o (List.Mem.tail a ho))]

/-- Frontier membership, characterized: a row is on the
    computed frontier exactly when it is in the table and no
    row of the table dominates it. -/
theorem notiff (b : Bool) : (!b) = true ↔ b = false := by
  cases b <;> decide

theorem frontiff (axes : List axis) (rows : List row) (r : row) :
    r ∈ front axes rows ↔
    r ∈ rows ∧ ∀ o ∈ rows, verdict axes o r = false := by
  simp only [front, List.mem_filter]
  constructor
  · intro h
    exact ⟨h.1, (anyfalse rows (fun o => verdict axes o r)).mp
      ((notiff _).mp h.2)⟩
  · intro h
    exact ⟨h.1, (notiff _).mpr
      ((anyfalse rows (fun o => verdict axes o r)).mpr h.2)⟩

theorem goodstep (d : Bool) (x y z : Nat) :
    good d x y = true → good d y z = true → good d x z = true := by
  intro h1 h2
  cases d with
  | true =>
    change decide (y ≤ x) = true at h1
    change decide (z ≤ y) = true at h2
    change decide (z ≤ x) = true
    exact decide_eq_true
      (Nat.le_trans (of_decide_eq_true h2) (of_decide_eq_true h1))
  | false =>
    change decide (x ≤ y) = true at h1
    change decide (y ≤ z) = true at h2
    change decide (x ≤ z) = true
    exact decide_eq_true
      (Nat.le_trans (of_decide_eq_true h1) (of_decide_eq_true h2))

theorem beatsstep (d : Bool) (x y z : Nat) :
    beats d x y = true → good d y z = true → beats d x z = true := by
  intro h1 h2
  simp only [beats, Bool.and_eq_true] at h1 ⊢
  refine ⟨goodstep d x y z h1.1 h2, ?_⟩
  have hnyx : good d y x = false := by
    cases hb : good d y x with
    | false => rfl
    | true =>
      rw [hb] at h1
      cases h1.2
  cases hb : good d z x with
  | false => rfl
  | true =>
    have hyx : good d y x = true := goodstep d y z x h2 hb
    rw [hyx] at hnyx
    cases hnyx

theorem coverstep : ∀ (axes : List axis) (xs ys zs : List Nat),
    xs.length = axes.length → ys.length = axes.length →
    zs.length = axes.length →
    cover axes xs ys = true → cover axes ys zs = true →
    cover axes xs zs = true := by
  intro axes
  induction axes with
  | nil =>
    intro xs ys zs hx hy hz _ _
    cases xs with
    | nil => rfl
    | cons x xs => simp at hx
  | cons a rest ih =>
    intro xs ys zs hx hy hz h1 h2
    cases xs with
    | nil => simp at hx
    | cons x xs =>
      cases ys with
      | nil => simp at hy
      | cons y ys =>
        cases zs with
        | nil => simp at hz
        | cons z zs =>
          have hx' : xs.length = rest.length := by simpa using hx
          have hy' : ys.length = rest.length := by simpa using hy
          have hz' : zs.length = rest.length := by simpa using hz
          simp only [cover, Bool.and_eq_true] at h1 h2 ⊢
          exact ⟨goodstep (dirv a) x y z h1.1 h2.1,
            ih xs ys zs hx' hy' hz' h1.2 h2.2⟩

theorem edgestep : ∀ (axes : List axis) (xs ys zs : List Nat),
    xs.length = axes.length → ys.length = axes.length →
    zs.length = axes.length →
    edge axes xs ys = true → cover axes ys zs = true →
    edge axes xs zs = true := by
  intro axes
  induction axes with
  | nil =>
    intro xs ys zs hx hy hz h _
    cases xs with
    | nil =>
      cases ys with
      | nil =>
        cases zs with
        | nil => cases h
        | cons z zs => simp at hz
      | cons y ys => simp at hy
    | cons x xs => simp at hx
  | cons a rest ih =>
    intro xs ys zs hx hy hz h1 h2
    cases xs with
    | nil => simp at hx
    | cons x xs =>
      cases ys with
      | nil => simp at hy
      | cons y ys =>
        cases zs with
        | nil => simp at hz
        | cons z zs =>
          have hx' : xs.length = rest.length := by simpa using hx
          have hy' : ys.length = rest.length := by simpa using hy
          have hz' : zs.length = rest.length := by simpa using hz
          simp only [cover, Bool.and_eq_true] at h2
          simp only [edge, Bool.or_eq_true] at h1 ⊢
          cases h1 with
          | inl hb => exact Or.inl (beatsstep (dirv a) x y z hb h2.1)
          | inr he => exact Or.inr (ih xs ys zs hx' hy' hz' he h2.2)

theorem verdictself (axes : List axis) (r : row) :
    verdict axes r r = false := by
  have h : decide (r.who ≠ r.who) = false := by simp
  simp [verdict, h]

theorem zipdiag : ∀ (axes : List axis) (xs : List Nat)
    (t : axis × Nat × Nat), t ∈ zip axes xs xs → t.2.1 = t.2.2 := by
  intro axes
  induction axes with
  | nil =>
    intro xs t ht
    cases xs with
    | nil => cases ht
    | cons x xs => cases ht
  | cons a rest ih =>
    intro xs t ht
    cases xs with
    | nil => cases ht
    | cons x xs =>
      cases ht with
      | head => rfl
      | tail _ hm => exact ih xs t hm

theorem beatself (d : Bool) (v : Nat) : beats d v v = false := by
  cases hb : good d v v <;> simp [beats, hb]

/-- Dominance is transitive, where the end rows are told apart
    by the uniqueness that obligation 1 gives the table: the
    extra hypothesis is exactly that uniqueness, for this pair. -/
theorem verdictstep (axes : List axis) (rx ry rz : row)
    (huniq : rx.who = rz.who → rx = rz) :
    verdict axes rx ry = true → verdict axes ry rz = true →
    verdict axes rx rz = true := by
  intro h1 h2
  have hwho : rx.who ≠ rz.who := by
    intro heq
    have hrr : rx = rz := huniq heq
    rw [← hrr] at h2
    simp only [verdict, Bool.and_eq_true, decide_eq_true_eq] at h1 h2
    have hedge : edge axes rx.vals rx.vals = true :=
      edgestep axes rx.vals ry.vals rx.vals h1.1.1.1.2 h1.1.1.2
        h1.1.1.1.2 h1.2 h2.1.2
    obtain ⟨t, ht, hb⟩ := (nine.edgeiff axes rx.vals rx.vals).mp hedge
    rw [zipdiag axes rx.vals t ht, beatself] at hb
    cases hb
  simp only [verdict, Bool.and_eq_true, decide_eq_true_eq] at h1 h2 ⊢
  exact ⟨⟨⟨⟨hwho, h1.1.1.1.2⟩, h2.1.1.2⟩,
    coverstep axes rx.vals ry.vals rz.vals h1.1.1.1.2 h1.1.1.2
      h2.1.1.2 h1.1.2 h2.1.2⟩,
    edgestep axes rx.vals ry.vals rz.vals h1.1.1.1.2 h1.1.1.2
      h2.1.1.2 h1.2 h2.1.2⟩

/-- The dominator count of a row in a row list: how many rows
    of the list dominate it. The termination measure of the
    completeness proof, counted from the list itself. -/
def count (p : row → Bool) : List row → Nat
  | [] => 0
  | a :: rest => (if p a = true then 1 else 0) + count p rest

theorem countle : ∀ (rows : List row) (p q : row → Bool),
    (∀ o ∈ rows, p o = true → q o = true) →
    count p rows ≤ count q rows := by
  intro rows
  induction rows with
  | nil => intro p q _; exact Nat.le_refl 0
  | cons a rest ih =>
    intro p q h
    have ih' := ih p q (fun o ho hp => h o (List.Mem.tail a ho) hp)
    simp only [count]
    by_cases ha : p a = true
    · have hqa : q a = true := h a (List.Mem.head rest) ha
      rw [if_pos ha, if_pos hqa]
      omega
    · have ha' : (if p a = true then 1 else 0) = 0 := if_neg ha
      by_cases hb : q a = true
      · rw [ha', if_pos hb]
        omega
      · rw [ha', if_neg hb]
        omega

theorem countpos : ∀ (rows : List row) (p : row → Bool) (o : row),
    o ∈ rows → p o = true → 0 < count p rows := by
  intro rows
  induction rows with
  | nil => intro p o h _; cases h
  | cons a rest ih =>
    intro p o h hp
    simp only [count]
    cases List.mem_cons.mp h with
    | inl e =>
      subst e
      rw [if_pos hp]
      omega
    | inr m =>
      have ih' := ih p o m hp
      by_cases ha : p a = true
      · rw [if_pos ha]; omega
      · rw [if_neg ha]; omega

/-- The dominator count strictly falls along a dominance step:
    every dominator of the dominator dominates the dominated
    row, and the dominator itself is counted for the dominated
    row but never for itself. This is where the derived
    finiteness of obligation 3 and the strictness in D5 do
    their work: the count is a natural number, so a strictly
    falling chain of dominators cannot run forever. -/
theorem countlt (axes : List axis) : ∀ (rows : List row) (r y : row),
    y ∈ rows → verdict axes y r = true →
    (∀ o ∈ rows, verdict axes o y = true → verdict axes o r = true) →
    count (fun o => verdict axes o y) rows <
    count (fun o => verdict axes o r) rows := by
  intro rows
  induction rows with
  | nil => intro r y h _ _; cases h
  | cons a rest ih =>
    intro r y hy hvy htrans
    by_cases hrest : y ∈ rest
    · have ih' := ih r y hrest hvy
        (fun o ho hv => htrans o (List.Mem.tail a ho) hv)
      simp only [count]
      by_cases ha : verdict axes a y = true
      · have har : verdict axes a r = true :=
          htrans a (List.Mem.head rest) ha
        rw [if_pos ha, if_pos har]
        omega
      · by_cases hb : verdict axes a r = true
        · rw [if_neg ha, if_pos hb]
          omega
        · rw [if_neg ha, if_neg hb]
          omega
    · have hay : y = a := by
        cases List.mem_cons.mp hy with
        | inl e => exact e
        | inr m => exact absurd m hrest
      have hle : count (fun o => verdict axes o y) rest ≤
          count (fun o => verdict axes o r) rest :=
        countle rest _ _ (fun o ho hv => htrans o (List.Mem.tail a ho) hv)
      simp only [count]
      have h1 : verdict axes a y = false := by
        rw [← hay]
        exact verdictself axes y
      have h2 : verdict axes a r = true := by
        rw [← hay]
        exact hvy
      rw [if_neg (by simp [h1] : ¬ verdict axes a y = true), if_pos h2]
      omega

end core

namespace ten

/-- Obligation 10, frontier soundness: every member of the
    computed frontier is undominated in the space. Hypotheses:
    none beyond obligations 1 and 9, both in content here: the
    frontier is read over the table rows (obligation 1's
    enumeration is what makes the rows the space), and the
    verdict is obligation 9's solver verdict. Proved from the
    pairwise verdicts over the whole space. -/
theorem sound (axes : List axis) (rows : List row) (r : row)
    (hr : r ∈ core.front axes rows) :
    ∀ o ∈ rows, verdict axes o r = false :=
  (core.frontiff axes rows r).mp hr |>.2

end ten

namespace eleven

/-- Obligation 11, frontier completeness, at row level: every
    candidate not on the computed frontier is dominated by a
    member of the computed frontier. The one hypothesis is the
    uniqueness conclusion of obligation 1 (one row per
    candidate), named here as it is used; the closed form over
    a space and table follows it. The proof follows a strictly
    ascending dominance chain: from a dominated row, move to a
    dominator; the dominator count, a natural number counted
    from the finite row list, strictly falls at each step
    (core.countlt), so the chain reaches an undominated row,
    which is a frontier member, and transitivity carries its
    dominance back to the start. -/
theorem complete (axes : List axis) (rows : List row)
    (huniq : ∀ r1 r2 : row, r1 ∈ rows → r2 ∈ rows →
      r1.who = r2.who → r1 = r2)
    (r : row) (hr : r ∈ rows) :
    r ∈ core.front axes rows ∨
    ∃ f ∈ core.front axes rows, verdict axes f r = true := by
  have claim : ∀ (n : Nat) (x : row), x ∈ rows →
      core.count (fun o => verdict axes o x) rows ≤ n →
      x ∈ core.front axes rows ∨
      ∃ f ∈ core.front axes rows, verdict axes f x = true := by
    intro n
    induction n with
    | zero =>
      intro x hx hcount
      left
      apply (core.frontiff axes rows x).mpr
      refine ⟨hx, fun o ho => ?_⟩
      by_cases hv : verdict axes o x = true
      · have hpos := core.countpos rows (fun o => verdict axes o x) o ho hv
        omega
      · cases hb : verdict axes o x with
        | false => rfl
        | true => exact absurd hb hv
    | succ k ih =>
      intro x hx hcount
      by_cases hfront : x ∈ core.front axes rows
      · exact Or.inl hfront
      · right
        have hany : rows.any (fun o => verdict axes o x) = true := by
          by_cases ha : rows.any (fun o => verdict axes o x) = true
          · exact ha
          · exfalso
            apply hfront
            apply (core.frontiff axes rows x).mpr
            refine ⟨hx, ?_⟩
            have hfalse : rows.any (fun o => verdict axes o x) = false := by
              cases hb : rows.any (fun o => verdict axes o x) with
              | false => rfl
              | true => exact absurd hb ha
            exact (core.anyfalse rows (fun o => verdict axes o x)).mp hfalse
        obtain ⟨y, hy, hvy⟩ := List.any_eq_true.mp hany
        have htrans : ∀ o ∈ rows, verdict axes o y = true →
            verdict axes o x = true :=
          fun o ho hv => core.verdictstep axes o y x
            (fun h => huniq o x ho hx h) hv hvy
        have hlt : core.count (fun o => verdict axes o y) rows <
            core.count (fun o => verdict axes o x) rows :=
          core.countlt axes rows x y hy hvy htrans
        obtain hcase := ih y hy (by omega)
        cases hcase with
        | inl hf => exact ⟨y, hf, hvy⟩
        | inr hdom =>
          obtain ⟨f, hf, hfy⟩ := hdom
          exact ⟨f, hf, core.verdictstep axes f y x
            (fun h => huniq f x ((core.frontiff axes rows f).mp hf).1 hx h)
            hfy hvy⟩
  exact claim (core.count (fun o => verdict axes o r) rows) r hr
    (Nat.le_refl _)

/-- Obligation 11, closed form: over a space and its pinned
    table, with obligation 1's checker pass as the hypothesis
    (hypothesis P3 in content, as lane 1 recorded it for
    obligation 1 itself). -/
theorem closed (s : space) (t : table) (ht : one.tally s t = true)
    (r : row) (hr : r ∈ t.rows) :
    r ∈ core.front s.axes t.rows ∨
    ∃ f ∈ core.front s.axes t.rows, verdict s.axes f r = true :=
  complete s.axes t.rows (one.enumeration s t ht).2 r hr

end eleven

namespace twelve

/-- The checker's frontier, read by the checker's own code
    path (the cross reading of obligation 9), never by the
    solver's verdict. -/
def front (axes : List axis) (rows : List row) : List row :=
  rows.filter (fun r => ! rows.any (fun o => cross axes o r))

/-- Obligation 12, general proof: the independent from-scratch
    checker, given only the pinned table and the definitions,
    computes a frontier set equal to the solver's frontier for
    the same table. Hypothesis P4 in content: the two readings
    share no component beyond the pinned table and the
    definitions — the checker frontier above is built from the
    cross reading alone, and the equality rests on obligation
    9's proof that each reading, separately, is D5. The
    executed instance comparison at the first instance's pin
    is lane 5's evidence, cited in the home record. -/
theorem equal (axes : List axis) (rows : List row) (r : row) :
    r ∈ front axes rows ↔ r ∈ core.front axes rows := by
  have hany : rows.any (fun o => cross axes o r) =
      rows.any (fun o => verdict axes o r) :=
    core.anyeq rows _ _ (fun o _ => (nine.agree axes o r).symm)
  simp only [front, core.front, List.mem_filter, hany]

end twelve

namespace thirteen

/-- Obligation 13, the assembled optimality theorem, stated at
    exactly the strength of section 1.1 and no stronger: at a
    pin where obligations 1 to 12 are closed (obligation 1's
    checker pass is the hypothesis here, in content P3 as lane
    1 recorded it; P1, P2, P4 are inherited in content from
    obligations 6, 9, and 12 exactly as those obligations carry
    them, and no additional hypothesis is taken), the named
    frontier is exactly the undominated set of the whole
    declared space, the checker frontier equals it, and no
    candidate outside it dominates a member of it. Assembly is
    from obligations 10, 11, and 12 alone. -/
theorem optimal (s : space) (t : table) (ht : one.tally s t = true)
    (r : row) (hr : r ∈ t.rows) :
    (r ∈ core.front s.axes t.rows ↔
      ∀ o ∈ t.rows, verdict s.axes o r = false) ∧
    (r ∉ core.front s.axes t.rows →
      ∃ f ∈ core.front s.axes t.rows, verdict s.axes f r = true) ∧
    (∀ x : row, x ∈ twelve.front s.axes t.rows ↔
      x ∈ core.front s.axes t.rows) ∧
    (∀ m ∈ core.front s.axes t.rows,
      ∀ o ∈ t.rows, verdict s.axes o m = false) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · constructor
    · intro h
      exact (core.frontiff s.axes t.rows r).mp h |>.2
    · intro h
      exact (core.frontiff s.axes t.rows r).mpr ⟨hr, h⟩
  · intro hnot
    cases eleven.closed s t ht r hr with
    | inl hf => exact absurd hf hnot
    | inr hd => exact hd
  · intro x
    exact twelve.equal s.axes t.rows x
  · intro m hm o ho
    exact ten.sound s.axes t.rows m hm o ho

end thirteen

namespace fifteen

/-- The cone of a frontier verdict: the full set of pairs it
    rests on, one pair per row of the table, taken jointly. -/
def cone (rows : List row) (r : row) : List (row × row) :=
  rows.map (fun o => (o, r))

/-- A frontier verdict is touched by a candidate when its cone
    contains a pair involving that candidate. -/
def touches (z : cand) (rows : List row) (r : row) : Prop :=
  ∃ p ∈ cone rows r, p.1.who = z ∨ p.2.who = z

/-- Obligation 15, exactness of the frontier cones: for a row
    of the table, its frontier verdict is touched by a
    candidate exactly when that candidate is in the table or
    is the row's own candidate. Read with the kept theorem
    below, this is the exactness the obligation names: the
    verdicts that can change under a join or a row change are
    exactly those whose cones contain a pair involving the
    joined or changed candidate — every frontier cone contains
    the pair from the changed row to its own row, so a change
    to a table row touches every frontier verdict (the first
    instance's control executed exactly this: 34 pair verdicts
    and all 18 frontier verdicts re-derived), and a change
    naming a candidate absent from the table touches none and
    certifies every frontier verdict unchanged. -/
theorem scope (rows : List row) (r : row) (hr : r ∈ rows) (z : cand) :
    touches z rows r ↔ (∃ o ∈ rows, o.who = z) ∨ r.who = z := by
  constructor
  · intro h
    obtain ⟨p, hp, hdis⟩ := h
    obtain ⟨o, ho, hop⟩ := List.mem_map.mp hp
    rw [← hop] at hdis
    cases hdis with
    | inl h => exact Or.inl ⟨o, ho, h⟩
    | inr h => exact Or.inr h
  · intro h
    cases h with
    | inl h =>
      obtain ⟨o, ho, hz⟩ := h
      exact ⟨(o, r), List.mem_map.mpr ⟨o, ho, rfl⟩, Or.inl hz⟩
    | inr h =>
      exact ⟨(r, r), List.mem_map.mpr ⟨r, hr, rfl⟩, Or.inr h⟩

theorem swapnone : ∀ (rows : List row) (z : cand) (n : row),
    (∀ o ∈ rows, o.who ≠ z) → fourteen.swap rows z n = rows := by
  intro rows
  induction rows with
  | nil => intro z n _; rfl
  | cons a rest ih =>
    intro z n h
    have ha : a.who ≠ z := h a (List.Mem.head rest)
    have ih' := ih z n (fun o ho => h o (List.Mem.tail a ho))
    simp only [fourteen.swap]
    rw [if_neg (show ¬ a.who = z from ha), ih']

/-- Obligation 15, the certified-unchanged half: a change
    naming a candidate that touches no frontier verdict (the
    scope theorem: absent from the table, and not the row's
    own) leaves the computed frontier exactly as it was. -/
theorem kept (axes : List axis) (rows : List row) (z : cand)
    (n : row)
    (h : ∀ o ∈ rows, o.who ≠ z) :
    core.front axes (fourteen.swap rows z n) = core.front axes rows := by
  rw [swapnone rows z n h]

end fifteen

namespace sixteen

/-- The cone certificate check: every element of the cone is
    present, identical, in the current table's cell list. -/
def holds (cur cone : List cell) : Bool :=
  cone.all (fun c => cur.any (fun d => decide (d = c)))

theorem member (cur cone : List cell) :
    holds cur cone = true ↔ ∀ c ∈ cone, c ∈ cur := by
  simp only [holds, List.all_eq_true, List.any_eq_true,
    decide_eq_true_eq]
  constructor
  · intro h c hc
    obtain ⟨d, hd, hdc⟩ := h c hc
    exact hdc ▸ hd
  · intro h c hc
    exact ⟨c, h c hc, rfl⟩

/-- Obligation 16, the carry: a verdict is reused only on a
    cone certificate. At the pair level the cone of a pair
    verdict is its two rows; when the current table's lookups
    for both candidates return the very rows the verdict was
    derived from — the certificate, at row level — the verdict
    read from the current table is the verdict carried, with
    no re-derivation. Hypotheses: P2 in content (a lookup
    returns the pinned table's row, as in obligation 9). -/
theorem carry (axes : List axis) (rows rows' : List row)
    (x y : cand) (rx ry : row)
    (hx : fourteen.find rows x = some rx)
    (hy : fourteen.find rows y = some ry)
    (hx' : fourteen.find rows' x = some rx)
    (hy' : fourteen.find rows' y = some ry) :
    (match fourteen.find rows' x, fourteen.find rows' y with
      | some a, some b => verdict axes a b
      | _, _ => false) =
    (match fourteen.find rows x, fourteen.find rows y with
      | some a, some b => verdict axes a b
      | _, _ => false) := by
  rw [hx, hy, hx', hy']

/-- Obligation 16, the refusal: a cone with exactly one changed
    cell refuses the carry, and the changed cell is named as
    the witness — the certificate fails, and some cone element
    (the changed one) is absent from the current table. -/
theorem refusal (cur cone : List cell) (c : cell)
    (hc : c ∈ cone) (hnot : c ∉ cur) :
    holds cur cone = false ∧ ∃ d ∈ cone, d ∉ cur := by
  refine ⟨?_, ⟨c, hc, hnot⟩⟩
  cases hb : holds cur cone with
  | false => rfl
  | true =>
    exfalso
    exact hnot ((member cur cone).mp hb c hc)

end sixteen

namespace seventeen

/-- The solver operations of section 5, reduced to the two
    that change the candidate set: join a candidate (join an
    axis measurement is a row change, a join of a replacement
    row after a withdrawal of the old one), and withdraw a
    candidate. Re-deriving one cone and answering a query do
    not change the state. -/
inductive op where
  | join : row → op
  | drop : cand → op
deriving DecidableEq, Repr

/-- The full, from-scratch state transition: what the checker
    sees. A join appends the row; a withdrawal filters the
    candidate out. Prior states are never edited: this builds
    the new state. -/
def apply (rows : List row) (o : op) : List row :=
  match o with
  | .join n => rows ++ [n]
  | .drop c => rows.filter (fun r => decide (r.who ≠ c))

/-- The incremental frontier update. A join re-derives exactly
    the frontier verdicts whose cones contain a pair involving
    the new candidate: the carried frontier members the new
    candidate dominates fall, the rest carry, and the new
    candidate joins the frontier exactly when no carried row
    dominates it. A withdrawal re-derives exactly the verdicts
    whose cones contained the withdrawn candidate: carried
    frontier members stay, and a remaining candidate is
    re-derived exactly when the withdrawn row dominated it and
    it was not already on the frontier. -/
def update (axes : List axis) (rows fr : List row) (o : op) : List row :=
  match o with
  | .join n => (fr.filter (fun f => ! verdict axes n f)) ++
      (if rows.any (fun x => verdict axes x n) then [] else [n])
  | .drop c =>
    match fourteen.find rows c with
    | none => fr
    | some d =>
      (fr.filter (fun f => decide (f.who ≠ c))) ++
      ((rows.filter (fun r => decide (r.who ≠ c))).filter
        (fun r => decide (verdict axes d r = true) &&
          decide (r ∉ fr) &&
          ! (rows.filter (fun r => decide (r.who ≠ c))).any
            (fun x => verdict axes x r)))

theorem findmem : ∀ (rows : List row) (c : cand) (d : row),
    fourteen.find rows c = some d → d ∈ rows ∧ d.who = c := by
  intro rows
  induction rows with
  | nil => intro c d h; cases h
  | cons a rest ih =>
    intro c d h
    by_cases ha : a.who = c
    · have h1 : fourteen.find (a :: rest) c = some a := by
        simp [fourteen.find, ha]
      rw [h1] at h
      cases h
      exact ⟨List.Mem.head rest, ha⟩
    · have h2 : fourteen.find (a :: rest) c = fourteen.find rest c := by
        simp [fourteen.find, ha]
      rw [h2] at h
      obtain ⟨hm, hw⟩ := ih c d h
      exact ⟨List.Mem.tail a hm, hw⟩

theorem findnone : ∀ (rows : List row) (c : cand),
    fourteen.find rows c = none → ∀ o ∈ rows, o.who ≠ c := by
  intro rows
  induction rows with
  | nil => intro c _ o h; cases h
  | cons a rest ih =>
    intro c h o ho
    by_cases ha : a.who = c
    · have h1 : fourteen.find (a :: rest) c = some a := by
        simp [fourteen.find, ha]
      rw [h1] at h
      cases h
    · have h2 : fourteen.find (a :: rest) c = fourteen.find rest c := by
        simp [fourteen.find, ha]
      rw [h2] at h
      cases List.mem_cons.mp ho with
      | inl e => rw [e]; exact ha
      | inr m => exact ih c h o m

theorem joinstep (axes : List axis) (rows fr : List row) (n : row)
    (hfr : ∀ y : row, y ∈ fr ↔ y ∈ core.front axes rows) (x : row) :
    x ∈ update axes rows fr (.join n) ↔
    x ∈ core.front axes (rows ++ [n]) := by
  have hup : update axes rows fr (.join n) =
      (fr.filter (fun f => ! verdict axes n f)) ++
      (if rows.any (fun o => verdict axes o n) then [] else [n]) := rfl
  rw [hup]
  have hforall : (∀ o ∈ rows ++ [n], verdict axes o x = false) ↔
      (∀ o ∈ rows, verdict axes o x = false) ∧
      verdict axes n x = false := by
    constructor
    · intro h
      refine ⟨fun o ho => h o (List.mem_append_left [n] ho), ?_⟩
      exact h n (List.mem_append_right rows (List.Mem.head []))
    · intro h o ho
      cases List.mem_append.mp ho with
      | inl hm => exact h.1 o hm
      | inr hm =>
        rw [List.mem_singleton.mp hm]
        exact h.2
  constructor
  · intro h
    apply (core.frontiff axes (rows ++ [n]) x).mpr
    cases List.mem_append.mp h with
    | inl hm =>
      obtain ⟨hxfr, hnx⟩ := List.mem_filter.mp hm
      obtain ⟨hxrows, hxall⟩ :=
        (core.frontiff axes rows x).mp ((hfr x).mp hxfr)
      have hnx' : verdict axes n x = false := by
        cases hb : verdict axes n x with
        | false => rfl
        | true =>
          rw [hb] at hnx
          cases hnx
      exact ⟨List.mem_append_left [n] hxrows,
        hforall.mpr ⟨hxall, hnx'⟩⟩
    | inr hm =>
      by_cases ha : rows.any (fun o => verdict axes o n) = true
      · rw [if_pos ha] at hm
        cases hm
      · rw [if_neg ha] at hm
        have hx : x = n := List.mem_singleton.mp hm
        subst hx
        have hall : ∀ o ∈ rows, verdict axes o x = false := by
          have hfalse : rows.any (fun o => verdict axes o x) = false := by
            cases hb : rows.any (fun o => verdict axes o x) with
            | false => rfl
            | true => exact absurd hb ha
          exact (core.anyfalse rows (fun o => verdict axes o x)).mp hfalse
        exact ⟨List.mem_append_right rows (List.Mem.head []),
          hforall.mpr ⟨hall, core.verdictself axes x⟩⟩
  · intro h
    obtain ⟨hxmem, hxall⟩ := (core.frontiff axes (rows ++ [n]) x).mp h
    obtain ⟨hxrows, hnx⟩ := hforall.mp hxall
    cases List.mem_append.mp hxmem with
    | inl hm =>
      apply List.mem_append_left
      apply List.mem_filter.mpr
      refine ⟨?_, ?_⟩
      · exact (hfr x).mpr ((core.frontiff axes rows x).mpr ⟨hm, hxrows⟩)
      · cases hb : verdict axes n x with
        | false => rfl
        | true => rw [hb] at hnx; cases hnx
    | inr hm =>
      have hx : x = n := List.mem_singleton.mp hm
      subst hx
      apply List.mem_append_right
      by_cases ha : rows.any (fun o => verdict axes o x) = true
      · obtain ⟨o, ho, hv⟩ := List.any_eq_true.mp ha
        rw [hxrows o ho] at hv
        cases hv
      · rw [if_neg ha]
        exact List.Mem.head []

theorem dropstep (axes : List axis) (rows fr : List row)
    (hfr : ∀ y : row, y ∈ fr ↔ y ∈ core.front axes rows)
    (huniq : ∀ r1 r2 : row, r1 ∈ rows → r2 ∈ rows →
      r1.who = r2.who → r1 = r2)
    (c : cand) (x : row) :
    x ∈ update axes rows fr (.drop c) ↔
    x ∈ core.front axes (apply rows (.drop c)) := by
  cases hfind : fourteen.find rows c with
  | none =>
    have hup : update axes rows fr (.drop c) = fr := by
      simp [update, hfind]
    rw [hup]
    have hne : ∀ o ∈ rows, o.who ≠ c := findnone rows c hfind
    have hmem : ∀ y : row, y ∈ apply rows (.drop c) ↔ y ∈ rows := by
      intro y
      simp only [apply, List.mem_filter, decide_eq_true_eq]
      constructor
      · intro h; exact h.1
      · intro h; exact ⟨h, hne y h⟩
    constructor
    · intro h
      have hxfront := (hfr x).mp h
      apply (core.frontiff axes (apply rows (.drop c)) x).mpr
      refine ⟨(hmem x).mpr ?_, fun o ho => ?_⟩
      · exact (core.frontiff axes rows x).mp hxfront |>.1
      · exact (core.frontiff axes rows x).mp hxfront |>.2 o ((hmem o).mp ho)
    · intro h
      obtain ⟨hxmem, hxall⟩ := (core.frontiff axes _ x).mp h
      apply (hfr x).mpr
      apply (core.frontiff axes rows x).mpr
      exact ⟨(hmem x).mp hxmem,
        fun o ho => hxall o ((hmem o).mpr ho)⟩
  | some d =>
    have hup : update axes rows fr (.drop c) =
        (fr.filter (fun f => decide (f.who ≠ c))) ++
        ((rows.filter (fun r => decide (r.who ≠ c))).filter
          (fun r => decide (verdict axes d r = true) &&
            decide (r ∉ fr) &&
            ! (rows.filter (fun r => decide (r.who ≠ c))).any
              (fun o => verdict axes o r))) := by
      simp [update, hfind]
    rw [hup]
    obtain ⟨hdmem, hdwho⟩ := findmem rows c d hfind
    have hrem : ∀ y : row, y ∈ apply rows (.drop c) ↔
        y ∈ rows ∧ y.who ≠ c := by
      intro y
      simp only [apply, List.mem_filter, decide_eq_true_eq]
    constructor
    · intro h
      apply (core.frontiff axes (apply rows (.drop c)) x).mpr
      cases List.mem_append.mp h with
      | inl hm =>
        obtain ⟨hxfr, hwho⟩ := List.mem_filter.mp hm
        have hwho' : x.who ≠ c := decide_eq_true_eq.mp hwho
        obtain ⟨hxrows, hxall⟩ :=
          (core.frontiff axes rows x).mp ((hfr x).mp hxfr)
        refine ⟨(hrem x).mpr ⟨hxrows, hwho'⟩, fun o ho => ?_⟩
        exact hxall o ((hrem o).mp ho).1
      | inr hm =>
        obtain ⟨hxrem, hcond⟩ := List.mem_filter.mp hm
        have hxrem' : x ∈ rows ∧ x.who ≠ c := (hrem x).mp hxrem
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
        refine ⟨hxrem, fun o ho => ?_⟩
        have hfalse : (apply rows (.drop c)).any
            (fun o => verdict axes o x) = false :=
          (core.notiff _).mp hcond.2
        exact (core.anyfalse _ (fun o => verdict axes o x)).mp hfalse o ho
    · intro h
      obtain ⟨hxrem, hxall⟩ := (core.frontiff axes _ x).mp h
      have hxrows : x ∈ rows := ((hrem x).mp hxrem).1
      have hxwho : x.who ≠ c := ((hrem x).mp hxrem).2
      by_cases hxfr : x ∈ fr
      · apply List.mem_append_left
        apply List.mem_filter.mpr
        exact ⟨hxfr, decide_eq_true hxwho⟩
      · obtain hcase := eleven.complete axes rows huniq x hxrows
        cases hcase with
        | inl hf => exact absurd hf (fun h => hxfr ((hfr x).mpr h))
        | inr hdom =>
          obtain ⟨f, hffr, hfx⟩ := hdom
          have hfrows : f ∈ rows :=
            (core.frontiff axes rows f).mp hffr |>.1
          have hfd : f = d := by
            by_cases hfc : f.who = c
            · exact huniq f d hfrows hdmem (hfc.trans hdwho.symm)
            · exfalso
              have hfrem : f ∈ apply rows (.drop c) :=
                (hrem f).mpr ⟨hfrows, hfc⟩
              rw [hxall f hfrem] at hfx
              cases hfx
          subst hfd
          apply List.mem_append_right
          apply List.mem_filter.mpr
          refine ⟨hxrem, ?_⟩
          simp only [Bool.and_eq_true, decide_eq_true_eq]
          refine ⟨⟨hfx, hxfr⟩, ?_⟩
          apply (core.notiff _).mpr
          exact (core.anyfalse _ (fun o => verdict axes o x)).mpr hxall

/-- An operation sequence, with its admissibility: a join is
    accepted only when the joined candidate is new to the
    current state (the entry refusal of obligation 2, as an
    operation condition). -/
def adm (rows : List row) : List op → Prop
  | [] => True
  | .join n :: os => n.who ∉ rows.map row.who ∧ adm (apply rows (.join n)) os
  | .drop c :: os => adm (apply rows (.drop c)) os

/-- The full walk: the state the checker computes, applying
    the operations from scratch at the end. -/
def walk (rows : List row) : List op → List row
  | [] => rows
  | o :: os => walk (apply rows o) os

/-- The incremental walk: the state and its maintained
    frontier, carried from operation to operation. -/
def track (axes : List axis) (rows fr : List row) :
    List op → List row × List row
  | [] => (rows, fr)
  | o :: os => track axes (apply rows o) (update axes rows fr o) os

theorem uniqjoin (rows : List row) (n : row)
    (huniq : ∀ r1 r2 : row, r1 ∈ rows → r2 ∈ rows →
      r1.who = r2.who → r1 = r2)
    (hn : n.who ∉ rows.map row.who) :
    ∀ r1 r2 : row, r1 ∈ apply rows (.join n) →
      r2 ∈ apply rows (.join n) → r1.who = r2.who → r1 = r2 := by
  intro r1 r2 h1 h2 hw
  cases List.mem_append.mp h1 with
  | inl hm1 =>
    cases List.mem_append.mp h2 with
    | inl hm2 => exact huniq r1 r2 hm1 hm2 hw
    | inr hm2 =>
      have hr2 : r2 = n := List.mem_singleton.mp hm2
      exfalso
      apply hn
      exact List.mem_map.mpr ⟨r1, hm1, hw.trans (congrArg row.who hr2)⟩
  | inr hm1 =>
    have hr1 : r1 = n := List.mem_singleton.mp hm1
    cases List.mem_append.mp h2 with
    | inl hm2 =>
      exfalso
      apply hn
      exact List.mem_map.mpr ⟨r2, hm2, hw.symm.trans (congrArg row.who hr1)⟩
    | inr hm2 =>
      have hr2 : r2 = n := List.mem_singleton.mp hm2
      rw [hr1, hr2]

theorem uniqdrop (rows : List row) (c : cand)
    (huniq : ∀ r1 r2 : row, r1 ∈ rows → r2 ∈ rows →
      r1.who = r2.who → r1 = r2) :
    ∀ r1 r2 : row, r1 ∈ apply rows (.drop c) →
      r2 ∈ apply rows (.drop c) → r1.who = r2.who → r1 = r2 := by
  intro r1 r2 h1 h2 hw
  exact huniq r1 r2 (List.mem_filter.mp h1).1 (List.mem_filter.mp h2).1 hw

/-- Obligation 17, incremental equals full: for the same
    version tuple and the same pinned table, the incrementally
    maintained frontier equals the from-scratch frontier, as
    sets, at every state of the space — proved by induction
    over the operation sequence of section 5, each operation
    preserving the equality (joinstep, dropstep). Hypothesis
    P4 in content, as in obligation 12: the full side is the
    checker frontier's own state sequence, and the equality at
    the final state is obligation 12's. The agreement evidence
    at the first instance is lane 4's 24 per-operation equality
    receipts and lane 5's 18 of 18 join replay, cited in the
    home record. -/
theorem equal (axes : List axis) : ∀ (ops : List op)
    (rows fr : List row),
    (∀ y : row, y ∈ fr ↔ y ∈ core.front axes rows) →
    (∀ r1 r2 : row, r1 ∈ rows → r2 ∈ rows →
      r1.who = r2.who → r1 = r2) →
    adm rows ops →
    (track axes rows fr ops).1 = walk rows ops ∧
    ∀ x : row, x ∈ (track axes rows fr ops).2 ↔
      x ∈ core.front axes (walk rows ops) := by
  intro ops
  induction ops with
  | nil =>
    intro rows fr hfr _ _
    exact ⟨rfl, fun x => hfr x⟩
  | cons o os ih =>
    intro rows fr hfr huniq hadm
    cases o with
    | join n =>
      obtain ⟨hn, hadm'⟩ := hadm
      have hstep : ∀ x : row,
          x ∈ update axes rows fr (.join n) ↔
          x ∈ core.front axes (apply rows (.join n)) :=
        fun x => joinstep axes rows fr n hfr x
      have huniq' := uniqjoin rows n huniq hn
      obtain ⟨h1, h2⟩ := ih (apply rows (.join n))
        (update axes rows fr (.join n)) hstep huniq' hadm'
      exact ⟨h1, h2⟩
    | drop c =>
      have hstep : ∀ x : row,
          x ∈ update axes rows fr (.drop c) ↔
          x ∈ core.front axes (apply rows (.drop c)) :=
        fun x => dropstep axes rows fr hfr huniq c x
      have huniq' := uniqdrop rows c huniq
      obtain ⟨h1, h2⟩ := ih (apply rows (.drop c))
        (update axes rows fr (.drop c)) hstep huniq' hadm
      exact ⟨h1, h2⟩

end seventeen

namespace eighteen

/-- The version tuple of D10: table pin, solver version,
    checker version, instrument version. -/
structure tuple where
  pin : Nat
  solver : Nat
  checker : Nat
  tool : Nat
deriving DecidableEq, Repr

/-- A verdict record: its value, and the tuple it was produced
    under. -/
structure record where
  under : tuple
  val : Bool
deriving DecidableEq, Repr

/-- Admission of a verdict for current use: only under the
    tuple in force. -/
def accept (cur : tuple) (r : record) : Bool :=
  decide (r.under = cur)

/-- Obligation 18, version binding: a verdict is accepted
    exactly when the tuple it was produced under is the tuple
    in force. -/
theorem binding (cur : tuple) (r : record) :
    accept cur r = true ↔ r.under = cur := by
  simp [accept]

/-- Obligation 18, the control's content: if any one component
    of the tuple differs — in particular exactly one — the
    verdict is not accepted: refusal, never acceptance by
    inheritance. -/
theorem changed (cur : tuple) (r : record)
    (h : r.under.pin ≠ cur.pin ∨ r.under.solver ≠ cur.solver ∨
      r.under.checker ≠ cur.checker ∨ r.under.tool ≠ cur.tool) :
    accept cur r = false := by
  cases hb : accept cur r with
  | false => rfl
  | true =>
    exfalso
    have heq : r.under = cur := (binding cur r).mp hb
    cases h with
    | inl hp => exact hp (by rw [heq])
    | inr h =>
      cases h with
      | inl hs => exact hs (by rw [heq])
      | inr h =>
        cases h with
        | inl hc => exact hc (by rw [heq])
        | inr ht => exact ht (by rw [heq])

end eighteen

namespace twenty

/-- The reopened set for a changed cell: exactly the verdict
    records whose cones contain that cell. -/
def reopen (k : Nat) (vs : List eight.verdictrec) :
    List eight.verdictrec :=
  vs.filter (fun v => decide (k ∈ v.cone))

/-- The kept set: the verdict records whose cones do not
    contain the changed cell. Their closure stands. -/
def kept (k : Nat) (vs : List eight.verdictrec) :
    List eight.verdictrec :=
  vs.filter (fun v => decide (k ∉ v.cone))

/-- Obligation 20, reopening is cone scoped: a verdict record
    reopens exactly when its cone contains the changed item,
    and every other record keeps its closure — the two sets
    partition the record list, with no third case. -/
theorem scope (k : Nat) (vs : List eight.verdictrec)
    (v : eight.verdictrec) :
    v ∈ reopen k vs ↔ v ∈ vs ∧ k ∈ v.cone := by
  simp [reopen]

theorem keptiff (k : Nat) (vs : List eight.verdictrec)
    (v : eight.verdictrec) :
    v ∈ kept k vs ↔ v ∈ vs ∧ k ∉ v.cone := by
  simp [kept]

theorem partition (k : Nat) (vs : List eight.verdictrec)
    (v : eight.verdictrec) (hv : v ∈ vs) :
    (v ∈ reopen k vs ∧ v ∉ kept k vs) ∨
    (v ∈ kept k vs ∧ v ∉ reopen k vs) := by
  by_cases hk : k ∈ v.cone
  · left
    refine ⟨(scope k vs v).mpr ⟨hv, hk⟩, ?_⟩
    rw [keptiff k vs v]
    intro h
    exact h.2 hk
  · right
    refine ⟨(keptiff k vs v).mpr ⟨hv, hk⟩, ?_⟩
    rw [scope k vs v]
    intro h
    exact hk h.2

end twenty
