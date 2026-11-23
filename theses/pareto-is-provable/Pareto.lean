/- Pareto proof program, lane 1: obligations 1 to 9 and 14 over the
   general definitions of section 0 of the methodology record of
   2026-11-22. Premises P1 to P4 stay explicit and are never
   discharged. Finiteness is derived, never a hypothesis. -/

/-- D1: an axis. Direction, scale and instrument are each optional
    in the raw record so that a missing part is representable and
    refusable; a usable axis has all parts present (obligation 5).
    The instrument is a named procedure (tool) at a named version
    (ver). The field at is the declaration time in graph order. -/
structure axis where
  name : Nat
  dir : Option Bool
  scale : Option Nat
  tool : Option Nat
  ver : Nat
  when : Nat
deriving DecidableEq, Repr

/-- D2: a candidate. A candidate with no description is not
    scorable and does not enter. -/
structure cand where
  name : Nat
  desc : Option Nat
deriving DecidableEq, Repr

/-- D3: a candidate space is a declared pair of written lists.
    The lists are the declaration act itself. -/
structure space where
  cands : List cand
  axes : List axis
deriving DecidableEq, Repr

/-- One row of the D4 table: a candidate and one value per axis,
    in axis order. -/
structure row where
  who : cand
  vals : List Nat
deriving DecidableEq, Repr

/-- D4: the pinned table. -/
structure table where
  rows : List row
  pin : Nat
deriving DecidableEq, Repr

/-- D9: a receipt. -/
structure receipt where
  who : Nat
  axis : Nat
  tool : Nat
  ver : Nat
  pin : Nat
  val : Nat
deriving DecidableEq, Repr

/-- One table cell, with its optional receipt (D4, obligation 6)
    and its graph order time. -/
structure cell where
  who : Nat
  axis : Nat
  val : Nat
  proof : Option receipt
  when : Nat
deriving DecidableEq, Repr

/-- D11: the three outcomes of every procedure. -/
inductive outcome where
  | accept : outcome
  | refuse : outcome
  | unmeasured : cell → outcome
deriving DecidableEq, Repr

/-- The direction an axis is read under; an undeclared direction
    defaults to higher-is-better only inside the dominance reading,
    and obligation 5 refuses such an axis before scoring. -/
def dirv (a : axis) : Bool := a.dir.getD true

/-- As good, per axis direction on the axis scale (D5), as a
    decidable value. -/
def good (d : Bool) (x y : Nat) : Bool :=
  if d then decide (y ≤ x) else decide (x ≤ y)

/-- Strictly better, per axis direction (D5). -/
def beats (d : Bool) (x y : Nat) : Bool :=
  good d x y && ! good d y x

/-- Every axis at least as good, read cell by cell over the three
    lists in step. -/
def cover : List axis → List Nat → List Nat → Bool
  | [], _, _ => true
  | _ :: _, [], _ => false
  | _ :: _, _, [] => false
  | a :: rest, x :: xs, y :: ys => good (dirv a) x y && cover rest xs ys

/-- At least one axis strictly better, read cell by cell. -/
def edge : List axis → List Nat → List Nat → Bool
  | [], _, _ => false
  | _ :: _, [], _ => false
  | _ :: _, _, [] => false
  | a :: rest, x :: xs, y :: ys => beats (dirv a) x y || edge rest xs ys

/-- The solver verdict for one ordered pair (D5 as a program).
    The length guards are D4: a row holds one value per axis. -/
def verdict (axes : List axis) (rx ry : row) : Bool :=
  decide (rx.who ≠ ry.who) && decide (rx.vals.length = axes.length) &&
  decide (ry.vals.length = axes.length) &&
  cover axes rx.vals ry.vals && edge axes rx.vals ry.vals

/-- The three lists zipped into one list of triples, for the
    independent reading of D5. -/
def zip : List axis → List Nat → List Nat → List (axis × Nat × Nat)
  | [], _, _ => []
  | _ :: _, [], _ => []
  | _ :: _, _, [] => []
  | a :: rest, x :: xs, y :: ys => (a, x, y) :: zip rest xs ys

/-- D5 stated over the zipped table: distinct candidates, at
    least as good on every axis, strictly better on at least
    one axis. No weights, no aggregate, no tie-break. -/
def dom (axes : List axis) (rx ry : row) : Prop :=
  rx.who ≠ ry.who ∧ rx.vals.length = axes.length ∧ ry.vals.length = axes.length ∧
  (∀ t ∈ zip axes rx.vals ry.vals, good (dirv t.1) t.2.1 t.2.2 = true) ∧
  (∃ t ∈ zip axes rx.vals ry.vals, beats (dirv t.1) t.2.1 t.2.2 = true)

/-- The checker reading of D5, by a separate code path over the
    zipped list: every entry good, some entry strict. -/
def cross (axes : List axis) (rx ry : row) : Bool :=
  decide (rx.who ≠ ry.who) && decide (rx.vals.length = axes.length) &&
  decide (ry.vals.length = axes.length) &&
  (zip axes rx.vals ry.vals).all (fun t => good (dirv t.1) t.2.1 t.2.2) &&
  (zip axes rx.vals ry.vals).any (fun t => beats (dirv t.1) t.2.1 t.2.2)

namespace nine

theorem coveriff : ∀ (axes : List axis) (xs ys : List Nat),
    xs.length = axes.length → ys.length = axes.length →
    (cover axes xs ys = true ↔
    ∀ t ∈ zip axes xs ys, good (dirv t.1) t.2.1 t.2.2 = true) := by
  intro axes
  induction axes with
  | nil =>
    intro xs ys hx hy
    cases xs with
    | nil =>
      cases ys with
      | nil => simp [cover, zip]
      | cons y ys => simp at hy
    | cons x xs => simp at hx
  | cons a rest ih =>
    intro xs ys hx hy
    cases xs with
    | nil => simp at hx
    | cons x xs =>
      cases ys with
      | nil => simp at hy
      | cons y ys =>
        have hx' : xs.length = rest.length := by
          simpa using hx
        have hy' : ys.length = rest.length := by
          simpa using hy
        simp only [cover, zip, Bool.and_eq_true]
        constructor
        · intro h t ht
          cases ht with
          | head => exact h.1
          | tail _ ht => exact ((ih xs ys hx' hy').mp h.2) t ht
        · intro h
          constructor
          · exact h (a, x, y) (by simp)
          · exact (ih xs ys hx' hy').mpr (fun t ht => h t (List.Mem.tail _ ht))

theorem edgeiff : ∀ (axes : List axis) (xs ys : List Nat),
    edge axes xs ys = true ↔
    ∃ t ∈ zip axes xs ys, beats (dirv t.1) t.2.1 t.2.2 = true := by
  intro axes
  induction axes with
  | nil => intro xs ys; simp [edge, zip]
  | cons a rest ih =>
    intro xs ys
    cases xs with
    | nil => simp [edge, zip]
    | cons x xs =>
      cases ys with
      | nil => simp [edge, zip]
      | cons y ys =>
        simp only [edge, zip, Bool.or_eq_true]
        constructor
        · intro h
          cases h with
          | inl h => exact ⟨(a, x, y), by simp, h⟩
          | inr h =>
            obtain ⟨t, ht, hb⟩ := (ih xs ys).mp h
            exact ⟨t, List.Mem.tail _ ht, hb⟩
        · intro h
          obtain ⟨t, ht, hb⟩ := h
          cases ht with
          | head => exact Or.inl hb
          | tail _ ht => exact Or.inr ((ih xs ys).mpr ⟨t, ht, hb⟩)

/-- Obligation 9, both directions: the solver verdict holds if
    and only if D5 holds of the pair on the pinned table. The
    hypothesis is P2 alone in content: the two rows read here are
    the pinned table's rows, and a pin names exactly one table
    state, so the rows are the table. -/
theorem pairwise (axes : List axis) (rx ry : row) :
    verdict axes rx ry = true ↔ dom axes rx ry := by
  simp only [verdict, dom, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · intro h
    exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2,
      (coveriff axes rx.vals ry.vals h.1.1.1.2 h.1.1.2).mp h.1.2,
      (edgeiff axes rx.vals ry.vals).mp h.2⟩
  · intro h
    exact ⟨⟨⟨⟨h.1, h.2.1⟩, h.2.2.1⟩,
      (coveriff axes rx.vals ry.vals h.2.1 h.2.2.1).mpr h.2.2.2.1⟩,
      (edgeiff axes rx.vals ry.vals).mpr h.2.2.2.2⟩

theorem crossiff (axes : List axis) (rx ry : row) :
    cross axes rx ry = true ↔ dom axes rx ry := by
  simp only [cross, dom, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.any_eq_true]
  constructor
  · intro h
    exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩
  · intro h
    exact ⟨⟨⟨⟨h.1, h.2.1⟩, h.2.2.1⟩, h.2.2.2.1⟩, h.2.2.2.2⟩

/-- Obligation 9, agreement form: the solver and the independent
    checker reading agree on every pair, as values. -/
theorem agree (axes : List axis) (rx ry : row) :
    verdict axes rx ry = cross axes rx ry := by
  rw [Bool.eq_iff_iff]
  constructor
  · intro h
    exact (crossiff axes rx ry).mpr ((pairwise axes rx ry).mp h)
  · intro h
    exact (pairwise axes rx ry).mpr ((crossiff axes rx ry).mp h)

end nine

namespace fourteen

/-- Row lookup in a table by candidate. -/
def find : List row → cand → Option row
  | [], _ => none
  | r :: rest, c => if r.who = c then some r else find rest c

/-- Replace the row of one candidate; every other row is shared
    by identity. -/
def swap : List row → cand → row → List row
  | [], _, _ => []
  | r :: rest, c, n => if r.who = c then n :: rest else r :: swap rest c n

theorem findswap : ∀ (rows : List row) (c x : cand) (n : row),
    n.who = c → x ≠ c → find (swap rows c n) x = find rows x := by
  intro rows
  induction rows with
  | nil => intro c x n _ _; rfl
  | cons r rest ih =>
    intro c x n hn hx
    by_cases h : r.who = c
    · have h1 : ¬ n.who = x := by
        rw [hn]; exact Ne.symm hx
      have h2 : ¬ r.who = x := by
        rw [h]; exact Ne.symm hx
      simp only [swap, find, h, if_true, if_neg h1, if_neg h2]
      rw [if_neg (show ¬ c = x from Ne.symm hx)]
    · have ih' := ih c x n hn hx
      simp only [swap, find, h, if_false]
      by_cases h3 : r.who = x
      · simp [h3]
      · simp [h3, ih']

/-- Obligation 14: the dominance verdict for an ordered pair
    rests only on the two candidates' rows. Changing any other
    candidate's row cannot change the pair's verdict. -/
theorem locality (axes : List axis) (rows : List row) (x y z : cand)
    (rx ry : row) (n : row) (hz : z ≠ x) (hz' : z ≠ y)
    (hn : n.who = z) (hx : find rows x = some rx) (hy : find rows y = some ry) :
    verdict axes rx ry =
      match find (swap rows z n) x, find (swap rows z n) y with
      | some a, some b => verdict axes a b
      | _, _ => false := by
  rw [findswap rows z x n hn (Ne.symm hz), findswap rows z y n hn (Ne.symm hz'), hx, hy]

end fourteen

/-- Finiteness of a predicate, witnessed by a written list.
    Used only as a conclusion, never as a hypothesis. -/
def fin {α : Type} (p : α → Prop) : Prop :=
  ∃ l : List α, ∀ x, p x ↔ x ∈ l

namespace three

/-- Obligation 3: finiteness is derived, not assumed. The
    declaration act is a written list; the space is that list;
    the list itself is the finiteness witness for both sets.
    No hypothesis of any kind is taken. -/
theorem finiteness (s : space) :
    fin (· ∈ s.cands) ∧ fin (· ∈ s.axes) :=
  ⟨⟨s.cands, fun _ => Iff.rfl⟩, ⟨s.axes, fun _ => Iff.rfl⟩⟩

end three

namespace one

/-- The enumeration checker for obligation 1: every row belongs
    to a declared candidate, every declared candidate has a row,
    and no candidate name repeats among rows. -/
def nodupb : List cand → Bool
  | [] => true
  | c :: cs => decide (c ∉ cs) && nodupb cs

def tally (s : space) (t : table) : Bool :=
  t.rows.all (fun r => decide (r.who ∈ s.cands)) &&
  s.cands.all (fun c => decide (c ∈ t.rows.map row.who)) &&
  nodupb (t.rows.map row.who)

theorem unique : ∀ (rows : List row) (r1 r2 : row),
    nodupb (rows.map row.who) = true →
    r1 ∈ rows → r2 ∈ rows → r1.who = r2.who → r1 = r2 := by
  intro rows
  induction rows with
  | nil => intro r1 r2 _ h1 _ _; cases h1
  | cons r rest ih =>
    intro r1 r2 hnd h1 h2 hw
    simp only [List.map_cons, nodupb, Bool.and_eq_true, decide_eq_true_eq] at hnd
    cases List.mem_cons.mp h1 with
    | inl e1 =>
      cases List.mem_cons.mp h2 with
      | inl e2 => rw [e1, e2]
      | inr m2 =>
        have hm : r2.who ∈ rest.map row.who :=
          List.mem_map.mpr ⟨r2, m2, rfl⟩
        have e1w : r1.who = r.who := congrArg row.who e1
        have step1 : r1.who ∈ rest.map row.who := hw ▸ hm
        have step2 : r.who ∈ rest.map row.who := e1w ▸ step1
        exact absurd step2 hnd.1
    | inr m1 =>
      cases List.mem_cons.mp h2 with
      | inl e2 =>
        have hm : r1.who ∈ rest.map row.who :=
          List.mem_map.mpr ⟨r1, m1, rfl⟩
        have e2w : r2.who = r.who := congrArg row.who e2
        have step1 : r2.who ∈ rest.map row.who := hw.symm ▸ hm
        have step2 : r.who ∈ rest.map row.who := e2w ▸ step1
        exact absurd step2 hnd.1
      | inr m2 => exact ih r1 r2 hnd.2 m1 m2 hw

/-- Obligation 1 (hypothesis P3, the scoping premise: the
    declared set is the space the claim speaks about): the
    declared candidate set and the table's row set are equal as
    sets, and each declared candidate has exactly one row. -/
theorem enumeration (s : space) (t : table) (h : tally s t = true) :
    (∀ c, c ∈ s.cands ↔ c ∈ t.rows.map row.who) ∧
    (∀ r1 r2 : row, r1 ∈ t.rows → r2 ∈ t.rows → r1.who = r2.who → r1 = r2) := by
  simp only [tally, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  constructor
  · intro c
    constructor
    · intro hc
      exact h.1.2 c hc
    · intro hc
      obtain ⟨r, hr, hwho⟩ := List.mem_map.mp hc
      have := h.1.1 r hr
      exact hwho ▸ this
  · intro r1 r2 h1 h2 hw
    exact unique t.rows r1 r2 h.2 h1 h2 hw

end one

namespace two

/-- A refusal reason (obligation 2). A duplicate refusal names
    the entered candidate it duplicates, in the field of. -/
inductive reason where
  | dupe : reason
  | blind : reason
  | barred : reason
deriving DecidableEq, Repr

/-- A disposition: entered, or refused with its reason. -/
inductive disp where
  | entered : disp
  | refused : reason → disp
deriving DecidableEq, Repr

/-- One entry log record. -/
structure entry where
  who : cand
  disp : disp
  of : Option cand
deriving DecidableEq, Repr

/-- The duplicate check for one log record against the log. -/
def dupok (log : List entry) (e : entry) : Bool :=
  match e.disp with
  | disp.refused reason.dupe =>
    match e.of with
    | some d => log.any (fun f => decide (f.who = d) && decide (f.disp = disp.entered))
    | none => false
  | _ => true

/-- The entry checker: the log's candidates are exactly the
    presentations, in order, and every duplicate refusal names
    an entered candidate in the log. -/
def accounted (pres : List cand) (log : List entry) : Bool :=
  decide (log.map entry.who = pres) && log.all (dupok log)

/-- Obligation 2: entry is total and accounted. Every presented
    candidate has exactly one recorded disposition (the log map
    is the presentation list itself), counts are equal, and
    every duplicate refusal names its entered candidate. -/
theorem ledger (pres : List cand) (log : List entry)
    (h : accounted pres log = true) :
    pres.length = log.length ∧
    (∀ c, c ∈ pres ↔ c ∈ log.map entry.who) ∧
    (∀ e ∈ log, e.disp = disp.refused reason.dupe →
      ∃ d f, e.of = some d ∧ f ∈ log ∧ f.who = d ∧ f.disp = disp.entered) := by
  simp only [accounted, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  refine ⟨?_, ?_, ?_⟩
  · rw [← h.1]
    simp
  · intro c
    rw [← h.1]
  · intro e he hd
    have hok : dupok log e = true := h.2 e he
    simp only [dupok, hd] at hok
    cases eof : e.of with
    | none => rw [eof] at hok; cases hok
    | some d =>
      rw [eof] at hok
      simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hok
      obtain ⟨f, hf, hfw, hfd⟩ := hok
      exact ⟨d, f, rfl, hf, hfw, hfd⟩

end two

namespace four

/-- One step of a version chain: withdraw, then enter. The prior
    version is never edited; this function builds the new one. -/
def evolve (old entered withdrawn : List cand) : List cand :=
  old.filter (fun c => decide (c ∉ withdrawn)) ++
  entered.filter (fun c => decide (c ∉ old))

/-- Obligation 4: the space changes only by declared entry or
    declared withdrawal. The set difference between successive
    pins is exactly the recorded entries minus the recorded
    withdrawals. -/
theorem change (old entered withdrawn : List cand) (c : cand) :
    c ∈ evolve old entered withdrawn ↔
    (c ∈ old ∧ c ∉ withdrawn) ∨ (c ∈ entered ∧ c ∉ old) := by
  simp [evolve]

end four

namespace five

/-- An axis is fully declared when all three parts are present:
    direction, scale, and instrument (the version is a number
    and always present). -/
def full (a : axis) : Prop :=
  a.dir.isSome ∧ a.scale.isSome ∧ a.tool.isSome

def fullb (a : axis) : Bool :=
  a.dir.isSome && a.scale.isSome && a.tool.isSome

/-- Obligation 5, declaration half: the checker pass over the
    declaration confirms all three parts for every axis. -/
theorem declared (s : space) (h : s.axes.all fullb = true) :
    ∀ a ∈ s.axes, full a := by
  rw [List.all_eq_true] at h
  intro a ha
  have hb := h a ha
  simp only [fullb, Bool.and_eq_true] at hb
  exact ⟨hb.1.1, hb.1.2, hb.2⟩

/-- The precedence checker: every axis declaration predates
    every value receipt on that axis, in graph order. -/
def earlier (s : space) (cells : List cell) : Bool :=
  s.axes.all (fun a => cells.all
    (fun c => if c.axis = a.name then decide (a.when < c.when) else true))

/-- Obligation 5, precedence half: where the checker passes,
    each axis was declared before the first value on it. -/
theorem timing (s : space) (cells : List cell)
    (h : earlier s cells = true) :
    ∀ a ∈ s.axes, ∀ c ∈ cells, c.axis = a.name → a.when < c.when := by
  simp only [earlier, List.all_eq_true] at h
  intro a ha c hc hname
  have h1 := h a ha c hc
  rw [if_pos hname] at h1
  exact decide_eq_true_eq.mp h1

end five

/-- The instrument: a named procedure, read as a function from
    tool number and candidate name to the value it produces.
    Any concrete instrument refines this reading. -/
def run (tool c : Nat) : Nat := tool * 1000 + c

/-- P1, instrument soundness, for one stamped relation: whatever
    the relation stamps is what the instrument produces. Stated
    as a hypothesis wherever used, never discharged. -/
def p1 (stamped : Nat → Nat → Nat → Prop) : Prop :=
  ∀ tool c v, stamped tool c v → v = run tool c

namespace six

/-- Obligation 6 (hypotheses P1 and P2): every cell carries a
    receipt naming candidate, axis, instrument, version, pin
    and value, and re-running the named instrument at the named
    version on the named candidate produces the cell's value.
    P2 enters as the receipt's pin being the table's pin: the
    pin names exactly this table state. -/
theorem binding (stamped : Nat → Nat → Nat → Prop) (hp1 : p1 stamped)
    (t : table) (c : cell) (r : receipt)
    (hrec : c.proof = some r) (hpin : r.pin = t.pin)
    (hwho : r.who = c.who) (hval : r.val = c.val)
    (hstamp : stamped r.tool c.who c.val) :
    run r.tool c.who = c.val ∧ r.pin = t.pin ∧ r.who = c.who ∧
    r.val = c.val ∧ c.proof = some r := by
  have h := hp1 r.tool c.who c.val hstamp
  exact ⟨h.symm, hpin, hwho, hval, hrec⟩

end six

namespace seven

/-- The cone procedure of obligation 7: walk the cone; the
    first unreceipted cell yields UNMEASURED naming that cell;
    a fully receipted cone accepts. -/
def assess : List cell → outcome
  | [] => outcome.accept
  | c :: cs => if c.proof.isNone then outcome.unmeasured c else assess cs

theorem gap : ∀ (cone : List cell) (c : cell),
    c ∈ cone → c.proof = none →
    ∃ d, assess cone = outcome.unmeasured d ∧ d ∈ cone ∧ d.proof = none := by
  intro cone
  induction cone with
  | nil => intro c h _; cases h
  | cons k cs ih =>
    intro c hc hnone
    by_cases hk : k.proof.isNone
    · refine ⟨k, ?_, List.Mem.head cs, ?_⟩
      · simp [assess, hk]
      · cases hp : k.proof with
        | none => rfl
        | some r => rw [hp] at hk; exact absurd hk Bool.false_ne_true
    · cases List.mem_cons.mp hc with
      | inl e =>
        rw [← e, hnone] at hk
        exact absurd rfl hk
      | inr m =>
        obtain ⟨d, hd, hdm, hdn⟩ := ih c m hnone
        refine ⟨d, ?_, List.Mem.tail k hdm, hdn⟩
        have hkf : k.proof.isNone = false := by
          cases hkk : k.proof.isNone with
          | true => exact absurd hkk hk
          | false => rfl
        simp [assess, hkf, hd]

/-- Obligation 7: no unreceipted value enters a derivation.
    A cone containing an unreceipted cell yields UNMEASURED
    naming a gap cell, and accept from no such cone. -/
theorem receipted (cone : List cell) (c : cell)
    (hc : c ∈ cone) (hnone : c.proof = none) :
    (∃ d, assess cone = outcome.unmeasured d ∧ d ∈ cone ∧ d.proof = none) ∧
    assess cone ≠ outcome.accept := by
  obtain ⟨d, hd, hdm, hdn⟩ := gap cone c hc hnone
  refine ⟨⟨d, hd, hdm, hdn⟩, ?_⟩
  rw [hd]
  intro hbad
  cases hbad

end seven

namespace eight

/-- A verdict record, for invalidation: its name and the axis
    names its cone contains. -/
structure verdictrec where
  name : Nat
  cone : List Nat
deriving DecidableEq, Repr

/-- Change an axis direction: a new axis version. The old
    version is withdrawn, the new one entered; nothing is
    edited in place. -/
def bump (a : axis) (d : Bool) : axis :=
  { a with dir := some d, ver := a.ver + 1 }

/-- Obligation 8, fixity: within one version tuple an axis has
    exactly one direction and one scale, because the axis is
    one record with one field of each kind. -/
theorem fixed (a : axis) (d1 d2 : Bool) (s1 s2 : Nat)
    (h1 : a.dir = some d1) (h2 : a.dir = some d2)
    (g1 : a.scale = some s1) (g2 : a.scale = some s2) :
    d1 = d2 ∧ s1 = s2 := by
  rw [h1] at h2
  rw [g1] at g2
  exact ⟨Option.some.inj h2, Option.some.inj g2⟩

/-- Obligation 8, versioning: a direction change is a new axis
    version, never the same axis. -/
theorem versioned (a : axis) (d : Bool) : bump a d ≠ a := by
  intro h
  have hv := congrArg axis.ver h
  simp [bump] at hv

/-- The invalidation set for a changed axis: exactly the
    verdicts whose cones contain a value on that axis. -/
def touched (a : axis) (vs : List verdictrec) : List verdictrec :=
  vs.filter (fun v => decide (a.name ∈ v.cone))

/-- Obligation 8, invalidation: the computed set is exactly the
    cone containing set. -/
theorem invalidated (a : axis) (vs : List verdictrec) (v : verdictrec) :
    v ∈ touched a vs ↔ v ∈ vs ∧ a.name ∈ v.cone := by
  simp [touched]

end eight
