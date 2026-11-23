import HypergraphIncremental

namespace SoftwareIsIncrementallySafe.OrderedIncrement

open Classical

def depGraph {σ : Type} (deps : σ → σ → Prop) (roots : σ → Prop) :
    HypergraphIncremental.Hypergraph σ where
  roots := roots
  edges := fun ps a => ∃ t, ps = [t] ∧ deps a t

theorem affected_root {σ : Type} {deps : σ → σ → Prop} {changed : σ → Bool} {s : σ}
    (h : changed s = true) :
    HypergraphIncremental.Affected (depGraph deps fun _ => False)
      (depGraph deps fun x => changed x = true) s :=
  .root (fun hr => hr.mpr h)

theorem affected_step {σ : Type} {deps : σ → σ → Prop} {changed : σ → Bool} {s t : σ}
    (hd : deps s t)
    (ht : HypergraphIncremental.Affected (depGraph deps fun _ => False)
      (depGraph deps fun x => changed x = true) t) :
    HypergraphIncremental.Affected (depGraph deps fun _ => False)
      (depGraph deps fun x => changed x = true) s :=
  .downstream ht (Or.inl ⟨[t], ⟨t, rfl, hd⟩, List.mem_singleton_self t⟩)

theorem affected_cases {σ : Type} {deps : σ → σ → Prop} {changed : σ → Bool} {s : σ}
    (h : HypergraphIncremental.Affected (depGraph deps fun _ => False)
      (depGraph deps fun x => changed x = true) s) :
    changed s = true ∨ ∃ t, deps s t ∧ HypergraphIncremental.Affected
      (depGraph deps fun _ => False) (depGraph deps fun x => changed x = true) t := by
  cases h with
  | root hr =>
    left
    cases hc : changed s with
    | true => rfl
    | false => exact (hr ⟨False.elim, fun he => Bool.noConfusion (hc.symm.trans he)⟩).elim
  | edge he => exact (he Iff.rfl).elim
  | @downstream p _ hp hd =>
    right
    rcases hd with ⟨ps, ⟨t, rfl, hdep⟩, hm⟩ | ⟨ps, ⟨t, rfl, hdep⟩, hm⟩ <;>
      · rw [List.mem_singleton] at hm
        subst hm
        exact ⟨p, hdep, hp⟩

theorem not_cone_not_changed {σ : Type} {deps : σ → σ → Prop} {changed : σ → Bool} {s : σ}
    (h : ¬ HypergraphIncremental.Affected (depGraph deps fun _ => False) (depGraph deps fun x => changed x = true) s) : changed s = false := by
  cases hc : changed s with
  | false => rfl
  | true => exact (h (affected_root hc)).elim

inductive DepStar {σ : Type} (deps : σ → σ → Prop) : σ → σ → Prop where
  | refl (s : σ) : DepStar deps s s
  | step {s t u : σ} : deps s t → DepStar deps t u → DepStar deps s u

def Local {σ C β : Type} (deps : σ → σ → Prop) (sem : (σ → C) → σ → β) : Prop :=
  ∀ (I I' : σ → C) (s : σ), (∀ t, DepStar deps s t → I t = I' t) → sem I s = sem I' s

def update {σ C : Type} (I : σ → C) (changed : σ → Bool) (new : σ → C) : σ → C :=
  fun s => if changed s then new s else I s

theorem update_unchanged {σ C : Type} {I : σ → C} {changed : σ → Bool} {new : σ → C}
    {s : σ} (h : changed s = false) : update I changed new s = I s := by
  simp [update, h]

theorem not_cone_closure_unchanged {σ : Type} {deps : σ → σ → Prop} {changed : σ → Bool}
    {s : σ} (h : ¬ HypergraphIncremental.Affected (depGraph deps fun _ => False) (depGraph deps fun x => changed x = true) s) : ∀ t, DepStar deps s t → changed t = false := by
  intro t hst
  revert h
  induction hst with
  | refl _ => exact fun h => not_cone_not_changed h
  | step hd _ ih => exact fun h => ih (fun hc => h (affected_step hd hc))

theorem outside_cone_stable {σ C β : Type} {deps : σ → σ → Prop} {sem : (σ → C) → σ → β}
    {I : σ → C} {changed : σ → Bool} {new : σ → C} {s : σ}
    (hLoc : Local deps sem) (h : ¬ HypergraphIncremental.Affected (depGraph deps fun _ => False) (depGraph deps fun x => changed x = true) s) :
    sem (update I changed new) s = sem I s :=
  hLoc _ _ s (fun t ht => update_unchanged (not_cone_closure_unchanged h t ht))

theorem recheck_iff_scratch {σ C β : Type} (deps : σ → σ → Prop) (sem : (σ → C) → σ → β)
    (Q : σ → β → Prop) (I : σ → C) (changed : σ → Bool) (new : σ → C)
    (hLoc : Local deps sem) (hOld : ∀ s, Q s (sem I s)) :
    (∀ s, HypergraphIncremental.Affected (depGraph deps fun _ => False) (depGraph deps fun x => changed x = true) s → Q s (sem (update I changed new) s)) ↔
      (∀ s, Q s (sem (update I changed new) s)) := by
  constructor
  · intro hc s
    by_cases h : HypergraphIncremental.Affected (depGraph deps fun _ => False) (depGraph deps fun x => changed x = true) s
    · exact hc s h
    · rw [outside_cone_stable hLoc h]
      exact hOld s
  · intro h s _
    exact h s

def applyAll {σ C : Type} (I : σ → C) : List ((σ → Bool) × (σ → C)) → (σ → C)
  | [] => I
  | (ch, nw) :: rest => applyAll (update I ch nw) rest

def ChainAccepted {σ C β : Type} (deps : σ → σ → Prop) (sem : (σ → C) → σ → β)
    (Q : σ → β → Prop) : (σ → C) → List ((σ → Bool) × (σ → C)) → Prop
  | _, [] => True
  | I, (ch, nw) :: rest =>
      (∀ s, HypergraphIncremental.Affected (depGraph deps fun _ => False) (depGraph deps fun x => ch x = true) s → Q s (sem (update I ch nw) s)) ∧
        ChainAccepted deps sem Q (update I ch nw) rest

theorem chain_recheck {σ C β : Type} (deps : σ → σ → Prop) (sem : (σ → C) → σ → β)
    (Q : σ → β → Prop) (hLoc : Local deps sem) :
    ∀ (ds : List ((σ → Bool) × (σ → C))) (I : σ → C),
      (∀ s, Q s (sem I s)) → ChainAccepted deps sem Q I ds →
        ∀ s, Q s (sem (applyAll I ds) s)
  | [], _, hOld, _ => hOld
  | (ch, nw) :: rest, I, hOld, ⟨hCone, hRest⟩ =>
      chain_recheck deps sem Q hLoc rest (update I ch nw)
        ((recheck_iff_scratch deps sem Q I ch nw hLoc hOld).mp hCone) hRest

abbrev Beh (ι ε : Type) := ι → List ε → Prop

def PrefixClosed {ε : Type} (P : List ε → Prop) : Prop :=
  ∀ t p, P t → p <+: t → P p

def TraceSafe {ι ε : Type} (P : List ε → Prop) (b : Beh ι ε) : Prop :=
  ∀ i t, b i t → P t

theorem traceSafe_prefixes {ι ε : Type} {P : List ε → Prop} (hP : PrefixClosed P)
    {b : Beh ι ε} (h : TraceSafe P b) : ∀ i t p, b i t → p <+: t → P p :=
  fun i t p ht hp => hP t p (h i t ht) hp

structure Flow (ι ε : Type) where
  lowEq : ι → ι → Prop
  lowView : List ε → List ε

def NI {ι ε : Type} (F : Flow ι ε) (b : Beh ι ε) : Prop :=
  ∀ i j, F.lowEq i j → ∀ t, b i t → ∃ t', b j t' ∧ F.lowView t' = F.lowView t

structure Spec (σ ι ε : Type) where
  safe : σ → List ε → Prop
  safe_prefixClosed : ∀ s, PrefixClosed (safe s)
  flow : σ → Flow ι ε

def Good {σ ι ε : Type} (S : Spec σ ι ε) (s : σ) (b : Beh ι ε) : Prop :=
  TraceSafe (S.safe s) b ∧ NI (S.flow s) b

def ReleaseGood {σ C ι ε : Type} (S : Spec σ ι ε) (sem : (σ → C) → σ → Beh ι ε)
    (I : σ → C) : Prop :=
  ∀ s, Good S s (sem I s)

def ConeGood {σ C ι ε : Type} (S : Spec σ ι ε) (deps : σ → σ → Prop)
    (sem : (σ → C) → σ → Beh ι ε) (I : σ → C) (changed : σ → Bool) (new : σ → C) : Prop :=
  ∀ s, HypergraphIncremental.Affected (depGraph deps fun _ => False) (depGraph deps fun x => changed x = true) s → Good S s (sem (update I changed new) s)

theorem ordered_incremental_iff_scratch {σ C ι ε : Type} (S : Spec σ ι ε)
    (deps : σ → σ → Prop) (sem : (σ → C) → σ → Beh ι ε)
    (I : σ → C) (changed : σ → Bool) (new : σ → C)
    (hLoc : Local deps sem) (hOld : ReleaseGood S sem I) :
    ConeGood S deps sem I changed new ↔ ReleaseGood S sem (update I changed new) :=
  recheck_iff_scratch deps sem (Good S) I changed new hLoc hOld

theorem ordered_safety_preserved {σ C ι ε : Type} (S : Spec σ ι ε)
    (deps : σ → σ → Prop) (sem : (σ → C) → σ → Beh ι ε)
    (I : σ → C) (changed : σ → Bool) (new : σ → C)
    (hLoc : Local deps sem) (hOld : ReleaseGood S sem I)
    (hCone : ConeGood S deps sem I changed new) :
    ∀ s i t, sem (update I changed new) s i t → S.safe s t :=
  fun s => ((ordered_incremental_iff_scratch S deps sem I changed new hLoc hOld).mp hCone s).1

theorem noninterference_preserved {σ C ι ε : Type} (S : Spec σ ι ε)
    (deps : σ → σ → Prop) (sem : (σ → C) → σ → Beh ι ε)
    (I : σ → C) (changed : σ → Bool) (new : σ → C)
    (hLoc : Local deps sem) (hOld : ReleaseGood S sem I)
    (hCone : ConeGood S deps sem I changed new) :
    ∀ s, NI (S.flow s) (sem (update I changed new) s) :=
  fun s => ((ordered_incremental_iff_scratch S deps sem I changed new hLoc hOld).mp hCone s).2

theorem ordered_chain {σ C ι ε : Type} (S : Spec σ ι ε)
    (deps : σ → σ → Prop) (sem : (σ → C) → σ → Beh ι ε) (hLoc : Local deps sem)
    (ds : List ((σ → Bool) × (σ → C))) (I : σ → C)
    (hOld : ReleaseGood S sem I) (hAcc : ChainAccepted deps sem (Good S) I ds) :
    ReleaseGood S sem (applyAll I ds) :=
  chain_recheck deps sem (Good S) hLoc ds I hOld hAcc

theorem refinement_preserves_traceSafe {ι ε : Type} (P : List ε → Prop) {b b' : Beh ι ε}
    (hR : ∀ i t, b' i t → b i t) (h : TraceSafe P b) : TraceSafe P b' :=
  fun i t ht => h i t (hR i t ht)

def leak : Beh Bool Bool := fun i t => t = [i]
def noise : Beh Bool Bool := fun _ t => t = [false] ∨ t = [true]

def openFlow : Flow Bool Bool := ⟨fun _ _ => True, id⟩

theorem leak_not_NI : ¬ NI openFlow leak := by
  intro h
  obtain ⟨t', ht', hv⟩ := h true false trivial [true] rfl
  simp only [leak] at ht'
  subst ht'
  simp [openFlow] at hv

theorem noise_NI : NI openFlow noise :=
  fun _ _ _ t ht => ⟨t, by cases ht <;> simp_all [noise], rfl⟩

theorem leak_refines_noise : ∀ i t, leak i t → noise i t := by
  intro i t h
  cases i <;> simp_all [leak, noise]

theorem refinement_does_not_preserve_NI :
    ¬ ∀ (b b' : Beh Bool Bool), (∀ i t, b' i t → b i t) → NI openFlow b → NI openFlow b' :=
  fun h => leak_not_NI (h noise leak leak_refines_noise noise_NI)

inductive Sym where
  | lib
  | app
  deriving DecidableEq

def symDeps : Sym → Sym → Prop := fun a b => a = .app ∧ b = .lib

def passSem : (Sym → Beh Bool Bool) → Sym → Beh Bool Bool
  | I, .lib => I .lib
  | I, .app => I .lib

theorem passSem_local : Local symDeps passSem := by
  intro I I' s h
  cases s with
  | lib => exact h .lib (DepStar.refl _)
  | app => exact h .lib (DepStar.step ⟨rfl, rfl⟩ (DepStar.refl _))

def passSpec : Spec Sym Bool Bool where
  safe := fun _ _ => True
  safe_prefixClosed := fun _ _ _ _ _ => trivial
  flow
    | .lib => ⟨fun _ _ => True, fun _ => []⟩
    | .app => openFlow

def oldCode : Sym → Beh Bool Bool := fun _ => noise
def newCode : Sym → Beh Bool Bool := fun _ => leak
def libChanged : Sym → Bool := fun s => decide (s = .lib)

theorem old_release_good : ReleaseGood passSpec passSem oldCode := by
  intro s
  refine ⟨fun _ _ _ => trivial, ?_⟩
  cases s with
  | lib => exact fun _ _ _ t ht => ⟨t, ht, rfl⟩
  | app => exact noise_NI

theorem changed_only_accepts :
    ∀ s, libChanged s = true → Good passSpec s (passSem (update oldCode libChanged newCode) s) := by
  intro s hs
  cases s with
  | app => simp [libChanged] at hs
  | lib =>
    exact ⟨fun _ _ _ => trivial, fun _ j _ _ _ =>
      ⟨[j], by simp [passSem, update, libChanged, newCode, leak], rfl⟩⟩

theorem new_release_leaks :
    ¬ NI (passSpec.flow .app) (passSem (update oldCode libChanged newCode) .app) := by
  have : passSem (update oldCode libChanged newCode) .app = leak := by
    funext i t
    simp [passSem, update, libChanged, newCode]
  rw [this]
  exact leak_not_NI

theorem new_refines_old :
    ∀ s i t, passSem (update oldCode libChanged newCode) s i t → passSem oldCode s i t := by
  intro s i t h
  cases s <;> simp [passSem, update, libChanged, newCode, oldCode] at h ⊢ <;>
    exact leak_refines_noise i t h

theorem naive_changed_only_false :
    ¬ ∀ (sem : (Sym → Beh Bool Bool) → Sym → Beh Bool Bool)
        (I new : Sym → Beh Bool Bool) (changed : Sym → Bool),
        Local symDeps sem → ReleaseGood passSpec sem I →
        (∀ s, changed s = true → Good passSpec s (sem (update I changed new) s)) →
        ReleaseGood passSpec sem (update I changed new) := by
  intro h
  exact new_release_leaks
    (h passSem oldCode newCode libChanged passSem_local old_release_good changed_only_accepts .app).2

theorem cone_recheck_refuses : ¬ ConeGood passSpec symDeps passSem oldCode libChanged newCode :=
  fun h => new_release_leaks (h .app (affected_step ⟨rfl, rfl⟩ (affected_root (by simp [libChanged])))).2

theorem missing_edge_cone_passes :
    ConeGood passSpec (fun _ _ => False) passSem oldCode libChanged newCode := by
  intro s hc
  rcases affected_cases hc with h | ⟨_, hd, _⟩
  · exact changed_only_accepts s h
  · exact hd.elim

theorem missing_edge_not_local : ¬ Local (fun _ _ => False : Sym → Sym → Prop) passSem := by
  intro h
  have hEq := h oldCode (update oldCode libChanged newCode) .app (by
    intro t ht
    cases ht with
    | refl => simp [update, libChanged]
    | step hd _ => exact hd.elim)
  have h2 := congrFun (congrFun hEq true) [false]
  simp [passSem, update, libChanged, oldCode, newCode, noise, leak] at h2

def doorOK : Bool → List String → Bool
  | _, [] => true
  | stopped, e :: es =>
    if e == "stop" then doorOK true es
    else if e == "open" then stopped && doorOK stopped es
    else doorOK stopped es

theorem doorOK_prefix (b : Bool) (p r : List String) :
    doorOK b (p ++ r) = true → doorOK b p = true := by
  induction p generalizing b with
  | nil => intro _; rfl
  | cons e es ih =>
    intro h
    simp only [List.cons_append, doorOK] at h ⊢
    split at h
    · rename_i he; simp only [he, if_true]; exact ih _ h
    · rename_i he
      simp only [he, if_false]
      split at h
      · rename_i ho
        simp only [ho, if_true, Bool.and_eq_true] at h ⊢
        simp only [Bool.false_eq_true, if_false, Bool.and_eq_true]
        exact ⟨h.1, ih _ h.2⟩
      · rename_i ho
        simp only [ho, if_false]
        exact ih _ h

theorem doorOK_prefixClosed : PrefixClosed (fun t : List String => doorOK false t = true) := by
  intro t p ht hp
  obtain ⟨r, hr⟩ := hp
  subst hr
  exact doorOK_prefix false p r ht

inductive DoorSym where
  | sensor
  | door
  deriving DecidableEq

def doorDepsP : DoorSym → DoorSym → Prop := fun a b => a = .door ∧ b = .sensor

def doorSemP : (DoorSym → Beh Unit String) → DoorSym → Beh Unit String
  | I, .sensor => I .sensor
  | I, .door => I .sensor

theorem doorSemP_local : Local doorDepsP doorSemP := by
  intro I I' s h
  cases s with
  | sensor => exact h .sensor (DepStar.refl _)
  | door => exact h .sensor (DepStar.step ⟨rfl, rfl⟩ (DepStar.refl _))

def doorSpec : Spec DoorSym Unit String where
  safe
    | .sensor => fun _ => True
    | .door => fun t => doorOK false t = true
  safe_prefixClosed
    | .sensor => fun _ _ _ _ => trivial
    | .door => doorOK_prefixClosed
  flow := fun _ => ⟨fun _ _ => True, id⟩

def stopOpen : DoorSym → Beh Unit String := fun _ _ t => t = ["stop", "open"]
def openStop : DoorSym → Beh Unit String := fun _ _ t => t = ["open", "stop"]
def sensorChanged : DoorSym → Bool := fun s => decide (s = .sensor)

theorem door_old_good : ReleaseGood doorSpec doorSemP stopOpen := by
  intro s
  refine ⟨?_, fun _ _ _ t ht => ⟨t, ht, rfl⟩⟩
  intro _ t ht
  cases s <;> simp only [doorSemP, stopOpen] at ht <;> subst ht <;> simp [doorSpec, doorOK]

theorem door_reordered_refused :
    ¬ ConeGood doorSpec doorDepsP doorSemP stopOpen sensorChanged openStop := by
  intro h
  have hd := (h .door (affected_step ⟨rfl, rfl⟩ (affected_root (by simp [sensorChanged])))).1 ()
    ["open", "stop"] (by simp [doorSemP, update, sensorChanged, openStop])
  simp [doorSpec, doorOK] at hd

theorem door_same_events (o : String) :
    (∃ t, stopOpen .door () t ∧ o ∈ t) ↔ (∃ t, openStop .door () t ∧ o ∈ t) := by
  simp [stopOpen, openStop, or_comm]

end SoftwareIsIncrementallySafe.OrderedIncrement
