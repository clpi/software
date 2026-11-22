import Audit.Definitional.Survivor

/-!
# Each conjunct of `survives` is needed

`survivesWith` switches one conjunct off at a time. With every switch on it is
`survives`. With any one switch off, a misjudgment from `Readings` comes back.
An earlier draft also required unique symbol ids in the candidate; no control
needed it and no soundness theorem used it, so it was dropped.
-/

namespace RegressAudit

structure Switches where
  allow : Bool := true
  prior : Bool := true
  cone : Bool := true
  removal : Bool := true

def behOkWith (w : Switches) (s : Spec) (n : Sym) : Bool :=
  (!w.prior || (s.prior n.id).all (fun b => decide (b ∈ n.beh))) &&
    (!w.allow || n.beh.all (fun b => decide (b ∈ s.allowed n.id))) &&
    decide (n.tLo ≤ n.tHi)

def symAdmitWith (w : Switches) (s : Spec) (inCone : Nat → Bool) (old : List Sym)
    (n : Sym) : Bool :=
  behOkWith w s n &&
    match lookup old n.id with
    | none => true
    | some o =>
      if !w.cone then true
      else if inCone n.id then decide (n.tHi ≤ o.tLo) else decide (n = o)

def survivesWith (w : Switches) (s : Spec) (inCone : Nat → Bool) (old new : List Sym) : Bool :=
  old.all (fun o => !w.removal || (s.prior o.id).isEmpty || (lookup new o.id).isSome) &&
    new.all (symAdmitWith w s inCone old)

theorem symAdmitWith_default (s : Spec) (c : Nat → Bool) (old : List Sym) :
    symAdmitWith {} s c old = symAdmit s c old := by
  funext n
  unfold symAdmitWith symAdmit behOkWith behOk
  cases lookup old n.id <;> simp

theorem survivesWith_default (s : Spec) (c : Nat → Bool) (old new : List Sym) :
    survivesWith {} s c old new = survives s c old new := by
  simp [survivesWith, survives, symAdmitWith_default]

theorem need_allow :
    survivesWith { allow := false } spec0 all base [⟨0, [ok, crash], 10, 10⟩] = true := by
  decide

theorem need_prior :
    survivesWith { prior := false } spec0 all base [⟨0, [], 10, 10⟩] = true := by decide

theorem need_cone :
    survivesWith { cone := false } spec0 all base [⟨0, [ok], 1000, 1000⟩] = true := by decide

theorem need_removal :
    survivesWith { removal := false } spec0 all base [] = true := by decide

/-- Swapping separation for the master gate's endpoint rule readmits the
repo's own slower-execution case. -/
def symAdmitEndpoints (s : Spec) (inCone : Nat → Bool) (old : List Sym) (n : Sym) : Bool :=
  behOk s n &&
    match lookup old n.id with
    | none => true
    | some o =>
      if inCone n.id then decide (n.tLo ≤ o.tLo) && decide (n.tHi ≤ o.tHi)
      else decide (n = o)

def survivesEndpoints (s : Spec) (inCone : Nat → Bool) (old new : List Sym) : Bool :=
  old.all (fun o => (s.prior o.id).isEmpty || (lookup new o.id).isSome) &&
    new.all (symAdmitEndpoints s inCone old)

theorem need_separation :
    survivesEndpoints spec0 all [⟨0, [ok], 10, 20⟩] [⟨0, [ok], 8, 18⟩] = true := by decide

/-- Keying by id is needed both ways: flattening behaviors across symbols
readmits the move (`r6_flat_blesses_move`), and keying by position refuses the
add-and-reorder release that `survives` accepts (`r2_head_condemns_reorder`,
`s_accepts_add_and_reorder`). -/
theorem keyed_not_flat :
    survives spec0 none' [⟨0, [ok], 10, 10⟩, ⟨1, [], 1, 1⟩]
        [⟨0, [], 10, 10⟩, ⟨1, [ok], 1, 1⟩] = false ∧
      specAdmit [ok] [ok] (flat [(0, []), (1, [ok])]) = true := by decide

end RegressAudit
