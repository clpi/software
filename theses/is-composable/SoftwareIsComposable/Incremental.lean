import SoftwareIsComposable.Admission
import HypergraphIncremental

namespace SoftwareIsComposable

def edgeOf (calls : List (Nat × Nat)) (ps : List Nat) (head : Nat) : Prop :=
  ∃ callee, ps = [callee] ∧ (head, callee) ∈ calls

def hyper (changed : List Nat) (calls : List (Nat × Nat)) :
    HypergraphIncremental.Hypergraph Nat where
  roots := fun s => s ∈ changed
  edges := fun ps head => edgeOf calls ps head

inductive InClosure (calls : List (Nat × Nat)) (changed : List Nat) : Nat → Prop
  | seed {s} : s ∈ changed → InClosure calls changed s
  | step {caller callee} : (caller, callee) ∈ calls →
      InClosure calls changed callee → InClosure calls changed caller

theorem inClosure_iff_affected {calls : List (Nat × Nat)} {changed : List Nat} {s : Nat} :
    InClosure calls changed s ↔
      HypergraphIncremental.Affected (hyper [] calls) (hyper changed calls) s := by
  constructor
  · intro h
    induction h with
    | @seed t hs =>
      apply HypergraphIncremental.Affected.root
      simpa [hyper] using hs
    | @step caller callee hcall _ ih =>
      apply HypergraphIncremental.Affected.downstream ih
      exact Or.inl (Exists.intro [callee] (And.intro
        (show (hyper [] calls).edges [callee] caller from
          Exists.intro callee (And.intro rfl hcall))
        (List.mem_cons.mpr (Or.inl rfl))))
  · intro h
    induction h with
    | @root a hr =>
      apply InClosure.seed
      simpa [hyper] using hr
    | edge he =>
      exact False.elim (he ⟨fun h => h, fun h => h⟩)
    | @downstream p a hp hdep ih =>
      rcases hdep with hdep | hdep
      · rcases hdep with ⟨ps, he, hm⟩
        simp [hyper, edgeOf] at he
        rcases he with ⟨callee, rfl, hcall⟩
        simp at hm
        cases hm
        exact InClosure.step hcall ih
      · rcases hdep with ⟨ps, he, hm⟩
        simp [hyper, edgeOf] at he
        rcases he with ⟨callee, rfl, hcall⟩
        simp at hm
        cases hm
        exact InClosure.step hcall ih

def symbolChecked (old new : Release) (s : Nat) : Prop :=
  ∀ p ∈ old.symbols, p.id = s →
    match new.symbols.find? (fun q => q.id == s) with
    | some q => SymbolAdmitted p q
    | none => False

theorem incrementalRecheck_iff {calls : List (Nat × Nat)} {changed : List Nat}
    {old new : Release}
    (hvalid : ∀ p ∈ old.symbols, ∀ b ∈ p.costs, b.lo ≤ b.hi)
    (stable : ∀ p ∈ old.symbols,
      ¬ HypergraphIncremental.Affected (hyper [] calls) (hyper changed calls) p.id →
        new.symbols.find? (fun q => q.id == p.id) = some p) :
    ReleaseAdmitted old new ↔
      ∀ s, HypergraphIncremental.Affected (hyper [] calls) (hyper changed calls) s →
        symbolChecked old new s := by
  constructor
  · intro hadm s _hs p hp hid
    have hadm' := hadm p hp
    have hfind : new.symbols.find? (fun q => q.id == p.id) =
        new.symbols.find? (fun q => q.id == s) := by
      simp [hid]
    simp [hfind] at hadm'
    exact hadm'
  · intro haff p hp
    by_cases ha : HypergraphIncremental.Affected (hyper [] calls) (hyper changed calls) p.id
    · have hchk := haff p.id ha p hp rfl
      exact hchk
    · have hfind := stable p hp ha
      simp [hfind]
      exact SymbolAdmitted.refl (hvalid p hp)

def seedOld : Release :=
  { symbols := [
      { id := 0, behaviors := [1], costs := [{ lo := 0, hi := 1 }] },
      { id := 1, behaviors := [5], costs := [{ lo := 0, hi := 1 }] }] }

def seedNew : Release :=
  { symbols := [
      { id := 0, behaviors := [1], costs := [{ lo := 0, hi := 1 }] },
      { id := 1, behaviors := [], costs := [{ lo := 0, hi := 1 }] }] }

theorem not_recheck_seed_only :
    releaseAdmitted seedOld seedNew = false ∧
      symbolAdmitted
        { id := 0, behaviors := [1], costs := [{ lo := 0, hi := 1 }] }
        { id := 0, behaviors := [1], costs := [{ lo := 0, hi := 1 }] } = true ∧
      InClosure [(1, 0)] [0] 1 ∧
      ¬ InClosure [(1, 0)] [0] 2 := by
  refine ⟨by decide, by decide, ?_, ?_⟩
  · exact InClosure.step (calls := [(1, 0)]) (changed := [0])
      (caller := 1) (callee := 0) (by simp) (InClosure.seed (by simp))
  · intro h
    cases h with
    | seed hs => simp at hs
    | step hcall _ => simp at hcall

end SoftwareIsComposable
