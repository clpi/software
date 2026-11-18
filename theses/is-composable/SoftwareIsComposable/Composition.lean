import SoftwareIsComposable.Admission

namespace SoftwareIsComposable

def kept (calls : List Call) (moduleOf : Nat → Nat) (exportOf : Nat → Nat)
    (stubCross : Bool) (id behavior : Nat) : Bool :=
  calls.all fun c =>
    if c.caller != id || c.behavior != behavior then true
    else if stubCross && moduleOf c.caller != moduleOf c.callee then true
    else exportOf c.callee == c.expected

def withKept (calls : List Call) (moduleOf : Nat → Nat) (exportOf : Nat → Nat)
    (stubCross : Bool) (p : SymbolProfile) : SymbolProfile :=
  { p with behaviors := p.behaviors.filter fun b => kept calls moduleOf exportOf stubCross p.id b }

def composeRelease (calls : List Call) (moduleOf : Nat → Nat) (exportOf : Nat → Nat)
    (stubCross : Bool) (r : Release) : Release :=
  { symbols := r.symbols.map (withKept calls moduleOf exportOf stubCross) }

def moduleSymbols (moduleOf : Nat → Nat) (m : Nat) (r : Release) : Release :=
  { symbols := r.symbols.filter fun p => moduleOf p.id == m }

theorem kept_stub_eq (calls : List Call) (moduleOf : Nat → Nat) (exportOf : Nat → Nat)
    (h : InteractionClosed moduleOf calls) (id behavior : Nat) :
    kept calls moduleOf exportOf true id behavior =
      kept calls moduleOf exportOf false id behavior := by
  induction calls with
  | nil => rfl
  | cons c cs ih =>
    have ih' := ih (fun d hd => h d (List.mem_cons.mpr (Or.inr hd)))
    simp only [kept] at ih'
    simp only [kept, List.all_cons]
    rw [ih']
    have hmod : moduleOf c.caller = moduleOf c.callee :=
      h c (List.mem_cons.mpr (Or.inl rfl))
    simp [hmod, Bool.and_true, Bool.and_false]

theorem withKept_stub (calls : List Call) (moduleOf : Nat → Nat) (exportOf : Nat → Nat)
    (h : InteractionClosed moduleOf calls) (p : SymbolProfile) :
    withKept calls moduleOf exportOf true p = withKept calls moduleOf exportOf false p := by
  simp [withKept, List.filter_congr (fun b _ => kept_stub_eq calls moduleOf exportOf h p.id b)]

theorem compose_stub (calls : List Call) (moduleOf : Nat → Nat) (exportOf : Nat → Nat)
    (h : InteractionClosed moduleOf calls) (r : Release) :
    composeRelease calls moduleOf exportOf true r =
      composeRelease calls moduleOf exportOf false r := by
  simp [composeRelease, List.map_congr_left (fun p _ => withKept_stub calls moduleOf exportOf h p)]

theorem module_compose_list (calls : List Call) (moduleOf : Nat → Nat) (exportOf : Nat → Nat)
    (stubCross : Bool) (m : Nat) (l : List SymbolProfile) :
    ((l.map (withKept calls moduleOf exportOf stubCross)).filter (fun p => moduleOf p.id == m)) =
      (l.filter (fun p => moduleOf p.id == m)).map (withKept calls moduleOf exportOf stubCross) := by
  induction l with
  | nil => simp
  | cons p ps ih =>
    by_cases h : moduleOf p.id = m
    · simp [h, beq_iff_eq, withKept, ih]
    · have hbeq : (moduleOf p.id == m) = false := by
        cases hb : moduleOf p.id == m with
        | true => exact absurd (beq_iff_eq.mp hb) h
        | false => rfl
      simp [hbeq, withKept, ih]

theorem module_compose_comm (calls : List Call) (moduleOf : Nat → Nat) (exportOf : Nat → Nat)
    (stubCross : Bool) (m : Nat) (r : Release) :
    moduleSymbols moduleOf m (composeRelease calls moduleOf exportOf stubCross r) =
      composeRelease calls moduleOf exportOf stubCross (moduleSymbols moduleOf m r) := by
  apply congrArg Release.mk
  simpa [moduleSymbols, composeRelease] using
    module_compose_list calls moduleOf exportOf stubCross m r.symbols

theorem pairwise_filter {moduleOf : Nat → Nat} {m : Nat} {l : List SymbolProfile}
    (hu : l.Pairwise fun a b => a.id ≠ b.id) :
    (l.filter fun q => moduleOf q.id == m).Pairwise fun a b => a.id ≠ b.id := by
  induction l with
  | nil => simp
  | cons a as ih =>
    rw [List.pairwise_cons] at hu
    simp [List.filter]
    split
    · rw [List.pairwise_cons]
      constructor
      · intro b hb
        have hb' : b ∈ as := by
          have hb'' := List.mem_filter.mp hb
          exact hb''.1
        exact hu.1 b hb'
      · exact ih hu.2
    · exact ih hu.2

theorem find?_filter_module {moduleOf : Nat → Nat} {m : Nat} {l : List SymbolProfile}
    {p : SymbolProfile} (hp : p ∈ l) (hm : moduleOf p.id = m)
    (hu : l.Pairwise fun a b => a.id ≠ b.id) :
    (l.filter fun q => moduleOf q.id == m).find? (fun q => q.id == p.id) = some p := by
  have hpf : p ∈ l.filter fun q => moduleOf q.id == m := by
    simp [List.mem_filter, beq_iff_eq, hp, hm]
  exact find?_eq_of_mem hpf (pairwise_filter hu)

theorem pairwise_map_id {l : List SymbolProfile} {f : SymbolProfile → SymbolProfile}
    (hf : ∀ p, (f p).id = p.id) (h : l.Pairwise fun a b => a.id ≠ b.id) :
    (l.map f).Pairwise fun a b => a.id ≠ b.id := by
  induction l with
  | nil => simp
  | cons a as ih =>
    rw [List.pairwise_cons] at h
    rw [List.map_cons, List.pairwise_cons]
    constructor
    · intro b hb
      rcases List.mem_map.mp hb with ⟨b0, hb0, rfl⟩
      simpa [hf] using h.1 b0 hb0
    · exact ih h.2

theorem partition_admits {moduleOf : Nat → Nat} {mods : List Nat} {old new : Release}
    (hcover : ∀ p ∈ old.symbols, moduleOf p.id ∈ mods)
    (huNew : UniqueIds new)
    (hmod : ∀ m ∈ mods,
      ReleaseAdmitted (moduleSymbols moduleOf m old) (moduleSymbols moduleOf m new)) :
    ReleaseAdmitted old new := by
  intro p hp
  have hm : moduleOf p.id ∈ mods := hcover p hp
  have hpM : p ∈ (moduleSymbols moduleOf (moduleOf p.id) old).symbols := by
    simp [moduleSymbols, List.mem_filter, beq_iff_eq, hm, hp]
  have hadm := hmod _ hm p hpM
  cases hfind : (moduleSymbols moduleOf (moduleOf p.id) new).symbols.find?
      (fun q => q.id == p.id) with
  | none => simp [hfind] at hadm
  | some q =>
    simp [hfind] at hadm
    have hqM : q ∈ (moduleSymbols moduleOf (moduleOf p.id) new).symbols :=
      mem_find? hfind
    have hq : q ∈ new.symbols := by
      simp [moduleSymbols, List.mem_filter] at hqM
      exact hqM.1
    have hid : p.id = q.id := by
      have hb := find?_pred (p := fun r : SymbolProfile => r.id == p.id) hfind
      exact (beq_iff_eq.mp hb).symm
    have hfull : new.symbols.find? (fun r => r.id == p.id) = some q := by
      have hfull := find?_eq_of_mem hq huNew
      have hpred : (fun r : SymbolProfile => r.id == p.id) = fun r => r.id == q.id := by
        funext r
        simp [hid]
      simpa [hpred] using hfull
    rw [hfull]
    exact hadm

theorem moduleAdmission_compose {moduleOf : Nat → Nat} {calls : List Call}
    {mods : List Nat} {oldExport newExport : Nat → Nat} {old new : Release}
    (hclosed : InteractionClosed moduleOf calls)
    (hcover : ∀ p ∈ old.symbols, moduleOf p.id ∈ mods)
    (huNew : UniqueIds new)
    (hmod : ∀ m ∈ mods,
      ReleaseAdmitted
        (composeRelease calls moduleOf oldExport true (moduleSymbols moduleOf m old))
        (composeRelease calls moduleOf newExport true (moduleSymbols moduleOf m new))) :
    ReleaseAdmitted
      (composeRelease calls moduleOf oldExport false old)
      (composeRelease calls moduleOf newExport false new) := by
  apply partition_admits (moduleOf := moduleOf) (mods := mods)
  · intro p hp
    simp [composeRelease] at hp
    rcases hp with ⟨p0, hp0, rfl⟩
    simp [withKept]
    exact hcover p0 hp0
  · simpa [UniqueIds, composeRelease] using
      pairwise_map_id (f := withKept calls moduleOf newExport false) (fun p => rfl) huNew
  · intro m hm
    have hold := compose_stub calls moduleOf oldExport hclosed (moduleSymbols moduleOf m old)
    have hnew := compose_stub calls moduleOf newExport hclosed (moduleSymbols moduleOf m new)
    have hold' := module_compose_comm calls moduleOf oldExport false m old
    have hnew' := module_compose_comm calls moduleOf newExport false m new
    have hadm := hmod m hm
    rw [hold] at hadm
    rw [← hold'] at hadm
    rw [hnew] at hadm
    rw [← hnew'] at hadm
    exact hadm

def crossModuleOf (id : Nat) : Nat := if id = 0 then 0 else 1

def crossCalls : List Call := [{ caller := 1, callee := 0, behavior := 5, expected := 1 }]

def crossOld : Release :=
  { symbols := [
      { id := 0, behaviors := [0], costs := [{ lo := 0, hi := 1 }] },
      { id := 1, behaviors := [5], costs := [{ lo := 0, hi := 1 }] }] }

def crossNew : Release := crossOld

def crossOldExport (id : Nat) : Nat := if id = 0 then 1 else 0

def crossNewExport (id : Nat) : Nat := if id = 0 then 2 else 0

theorem moduleAdmission_counterexample :
    ¬ InteractionClosed crossModuleOf crossCalls ∧
      releaseAdmitted
        (composeRelease crossCalls crossModuleOf crossOldExport true
          (moduleSymbols crossModuleOf 0 crossOld))
        (composeRelease crossCalls crossModuleOf crossNewExport true
          (moduleSymbols crossModuleOf 0 crossNew)) = true ∧
      releaseAdmitted
        (composeRelease crossCalls crossModuleOf crossOldExport true
          (moduleSymbols crossModuleOf 1 crossOld))
        (composeRelease crossCalls crossModuleOf crossNewExport true
          (moduleSymbols crossModuleOf 1 crossNew)) = true ∧
      releaseAdmitted
        (composeRelease crossCalls crossModuleOf crossOldExport false crossOld)
        (composeRelease crossCalls crossModuleOf crossNewExport false crossNew) = false := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    have hcall : crossModuleOf 1 = crossModuleOf 0 :=
      h { caller := 1, callee := 0, behavior := 5, expected := 1 } (by simp [crossCalls])
    simp [crossModuleOf] at hcall
  · decide
  · decide
  · decide

end SoftwareIsComposable
