import SoftwareIsComposable.Admission
import FiniteFrontier

namespace SoftwareIsComposable

def hiCost (p : SymbolProfile) (axis : Nat) : Int :=
  match p.costs[axis]? with
  | some b => (b.hi : Int)
  | none => 0

theorem qualifiedMono {old new : Release} (h : ReleaseAdmitted old new)
    {p : SymbolProfile} (hp : p ∈ old.symbols) :
    ∃ q, new.symbols.find? (fun r => r.id == p.id) = some q ∧
      accepts p.behaviors q.behaviors = true := by
  cases hfind : new.symbols.find? (fun r => r.id == p.id) with
  | none =>
    have hp' := h p hp
    simp [hfind] at hp'
  | some q =>
    refine ⟨q, rfl, ?_⟩
    have hp' : SymbolAdmitted p q := by
      have hadm := h p hp
      rw [hfind] at hadm
      exact hadm
    exact (accepts_iff).mpr hp'.keeps

theorem qualifiedTrans {a b c : Release}
    (hab : ReleaseAdmitted a b) (hbc : ReleaseAdmitted b c)
    {p : SymbolProfile} (hp : p ∈ a.symbols) {beh : Nat} (hb : beh ∈ p.behaviors) :
    ∃ q, c.symbols.find? (fun r => r.id == p.id) = some q ∧ beh ∈ q.behaviors := by
  obtain ⟨q, hfind, hacc⟩ := qualifiedMono (releaseAdmitted_trans hab hbc) hp
  exact ⟨q, hfind, (accepts_iff).mp hacc beh hb⟩

theorem costNoRegression {old new : SymbolProfile} (h : SymbolAdmitted old new)
    (axes : List Nat) (hall : ∀ a ∈ axes, a < old.costs.length) :
    FiniteFrontier.strictPareto axes hiCost old new = false := by
  cases hsp : FiniteFrontier.strictPareto axes hiCost old new with
  | false => rfl
  | true =>
    have hiff := (FiniteFrontier.pareto_exact axes hiCost old new).mp hsp
    rcases hiff with ⟨hle, i, hi, hlt⟩
    have hii : i < old.costs.length := hall i hi
    have hii' : i < new.costs.length := by rw [← h.costLen]; exact hii
    have hmem := zip_get h.costLen i hii
    have hdown : (new.costs[i]'hii').hi ≤ (old.costs[i]'hii).hi := h.costHi _ hmem
    have hupI : ((old.costs[i]'hii).hi : Int) ≤ (new.costs[i]'hii').hi := by
      simpa [hiCost, List.getElem?_eq_getElem hii, List.getElem?_eq_getElem hii'] using hle i hi
    have hltI : ((old.costs[i]'hii).hi : Int) < (new.costs[i]'hii').hi := by
      simpa [hiCost, List.getElem?_eq_getElem hii, List.getElem?_eq_getElem hii'] using hlt
    have hup : (old.costs[i]'hii).hi ≤ (new.costs[i]'hii').hi := Int.ofNat_le.mp hupI
    have hltN : (old.costs[i]'hii).hi < (new.costs[i]'hii').hi := Int.ofNat_lt.mp hltI
    have heq : (old.costs[i]'hii).hi = (new.costs[i]'hii').hi := Nat.le_antisymm hup hdown
    omega

theorem costTrans {a b c : SymbolProfile}
    (h1 : SymbolAdmitted a b) (h2 : SymbolAdmitted b c)
    (i : Nat) (hi : i < a.costs.length) :
    ∀ bc ba, c.costs[i]? = some bc → a.costs[i]? = some ba → bc.hi ≤ ba.hi := by
  have h := symbolAdmitted_trans h1 h2
  have hi' : i < c.costs.length := by rw [← h.costLen]; exact hi
  intro bc ba hbc hba
  have hmem := zip_get h.costLen i hi
  have hle := h.costHi _ hmem
  simp [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hi'] at hba hbc
  subst hba
  subst hbc
  exact hle

def boundOld : SymbolProfile :=
  { id := 0, behaviors := [1], costs := [{ lo := 1, hi := 100 }] }

def boundNew : SymbolProfile :=
  { id := 0, behaviors := [1], costs := [{ lo := 2, hi := 3 }] }

theorem bound_step_admitted : symbolAdmitted boundOld boundNew = true := by
  decide

theorem not_per_execution :
    ¬ ∀ x y : Nat, (1 ≤ x ∧ x ≤ 100) → (2 ≤ y ∧ y ≤ 3) → y ≤ x := by
  intro h
  have := h 1 3 (by omega) (by omega)
  omega

end SoftwareIsComposable
