import SoftwareIsIncrementallySafe

open SoftwareIsComposable
open SoftwareIsIncrementallySafe

namespace AuditDependencyModules

theorem cone_sound {calls : List (Nat × Nat)} {seeds : List Nat} {s : Nat}
    (h : s ∈ coneExecOf calls seeds) : InClosure calls seeds s :=
  coneExec_sound h

theorem cone_complete {calls : List (Nat × Nat)} {seeds : List Nat} {s : Nat}
    (h : InClosure calls seeds s) : s ∈ coneExecOf calls seeds :=
  coneExec_complete h

theorem cone_affected {calls : List (Nat × Nat)} {seeds : List Nat} {s : Nat} :
    s ∈ coneExecOf calls seeds ↔
      HypergraphIncremental.Affected (hyper [] calls) (hyper seeds calls) s :=
  coneExec_iff_affected

theorem closureHyp_is_inClosure (calls : List (Nat × Nat)) (seeds inspected : List Nat) :
    ClosureHyp calls seeds inspected ↔ ∀ s, InClosure calls seeds s → s ∈ inspected :=
  Iff.rfl

theorem coneGood_is_affected {σ C ι ε : Type} (S : OrderedIncrement.Spec σ ι ε)
    (deps : σ → σ → Prop) (sem : (σ → C) → σ → OrderedIncrement.Beh ι ε)
    (I : σ → C) (changed : σ → Bool) (new : σ → C) :
    OrderedIncrement.ConeGood S deps sem I changed new ↔
      ∀ s, HypergraphIncremental.Affected (OrderedIncrement.depGraph deps fun _ => False)
          (OrderedIncrement.depGraph deps fun t => changed t = true) s →
        OrderedIncrement.Good S s (sem (OrderedIncrement.update I changed new) s) :=
  Iff.rfl

theorem same_profile_pareto :
    SoftwareIsQuantifiable.Pareto.profileOf (outputPoint leakBit) =
      SoftwareIsQuantifiable.Pareto.profileOf (outputPoint noiseBit) :=
  same_profile

theorem outputPoint_faithful (f g : Bool → Bool → Prop) :
    outputPoint f = outputPoint g ↔ (fun o => ∃ s, f s o) = (fun o => ∃ s, g s o) :=
  outputPoint_eq_iff f g

end AuditDependencyModules

namespace AuditDependencyModules.Legacy

inductive StringCone (deps : List (String × String)) (seeds : List String) : String → Prop where
  | root {s : String} : s ∈ seeds → StringCone deps seeds s
  | step {s t : String} : (s, t) ∈ deps → StringCone deps seeds t → StringCone deps seeds s

inductive OrderedCone {σ : Type} (deps : σ → σ → Prop) (changed : σ → Bool) : σ → Prop where
  | root {s : σ} : changed s = true → OrderedCone deps changed s
  | step {s t : σ} : deps s t → OrderedCone deps changed t → OrderedCone deps changed s

theorem stringCone_iff_inClosure (e : Nat → String) (he : ∀ a b, e a = e b → a = b)
    (calls : List (Nat × Nat)) (seeds : List Nat) (s : Nat) :
    StringCone (calls.map fun c => (e c.1, e c.2)) (seeds.map e) (e s) ↔
      InClosure calls seeds s := by
  constructor
  · intro h
    suffices H : ∀ x, StringCone (calls.map fun c => (e c.1, e c.2)) (seeds.map e) x →
        ∀ n, x = e n → InClosure calls seeds n from H _ h s rfl
    intro x hx
    induction hx with
    | root hm =>
      intro n hn
      subst hn
      rcases List.mem_map.mp hm with ⟨a, ha, hae⟩
      rw [he a n hae] at ha
      exact InClosure.seed ha
    | step hd _ ih =>
      intro n hn
      subst hn
      rcases List.mem_map.mp hd with ⟨⟨a, b⟩, hab, heq⟩
      simp only [Prod.mk.injEq] at heq
      rw [he a n heq.1] at hab
      exact InClosure.step hab (ih b heq.2.symm)
  · intro h
    induction h with
    | seed hm => exact StringCone.root (List.mem_map_of_mem hm)
    | step hc _ ih => exact StringCone.step (List.mem_map_of_mem (f := fun c => (e c.1, e c.2)) hc) ih

theorem stringCone_iff_affected (e : Nat → String) (he : ∀ a b, e a = e b → a = b)
    (calls : List (Nat × Nat)) (seeds : List Nat) (s : Nat) :
    StringCone (calls.map fun c => (e c.1, e c.2)) (seeds.map e) (e s) ↔
      HypergraphIncremental.Affected (hyper [] calls) (hyper seeds calls) s :=
  (stringCone_iff_inClosure e he calls seeds s).trans inClosure_iff_affected

theorem orderedCone_iff_affected {σ : Type} (deps : σ → σ → Prop) (changed : σ → Bool) (s : σ) :
    OrderedCone deps changed s ↔
      HypergraphIncremental.Affected (OrderedIncrement.depGraph deps fun _ => False)
        (OrderedIncrement.depGraph deps fun x => changed x = true) s := by
  constructor
  · intro h
    induction h with
    | root hc => exact OrderedIncrement.affected_root hc
    | step hd _ ih => exact OrderedIncrement.affected_step hd ih
  · intro h
    induction h with
    | root hr =>
      rename_i a
      cases hc : changed a with
      | true => exact OrderedCone.root hc
      | false => exact (hr ⟨False.elim, fun he => Bool.noConfusion (hc.symm.trans he)⟩).elim
    | edge he => exact (he Iff.rfl).elim
    | @downstream p a _ hd ih =>
      rcases hd with ⟨ps, ⟨t, rfl, hdep⟩, hm⟩ | ⟨ps, ⟨t, rfl, hdep⟩, hm⟩ <;>
        · rw [List.mem_singleton] at hm
          subst hm
          exact OrderedCone.step hdep ih

end AuditDependencyModules.Legacy

namespace AuditDependencyModules.Mutation

open SoftwareIsIncrementallySafe.OrderedIncrement

theorem mut_drop_hLoc :
    ¬ ∀ {σ C ι ε : Type} (S : Spec σ ι ε) (deps : σ → σ → Prop) (sem : (σ → C) → σ → Beh ι ε)
        (I : σ → C) (changed : σ → Bool) (new : σ → C),
        ReleaseGood S sem I →
        (ConeGood S deps sem I changed new ↔ ReleaseGood S sem (update I changed new)) := by
  intro h
  have := (h passSpec (fun _ _ => False) passSem oldCode libChanged newCode old_release_good).mp
    missing_edge_cone_passes
  exact new_release_leaks (this .app).2

theorem mut_drop_hOld :
    ¬ ∀ {σ C ι ε : Type} (S : Spec σ ι ε) (deps : σ → σ → Prop) (sem : (σ → C) → σ → Beh ι ε)
        (I : σ → C) (changed : σ → Bool) (new : σ → C),
        Local deps sem →
        (ConeGood S deps sem I changed new ↔ ReleaseGood S sem (update I changed new)) := by
  intro h
  have hno : ∀ s, ¬ Legacy.OrderedCone symDeps (fun _ : Sym => false) s := by
    intro s hc
    induction hc with
    | root hr => simp at hr
    | step _ _ ih => exact ih
  have hv : ConeGood passSpec symDeps passSem newCode (fun _ => false) newCode :=
    fun s hc => (hno s ((Legacy.orderedCone_iff_affected _ _ s).mpr hc)).elim
  have hr := (h passSpec symDeps passSem newCode (fun _ => false) newCode passSem_local).mp hv
  apply leak_not_NI
  have := (hr .app).2
  simpa [passSem, update, newCode, passSpec] using this

end AuditDependencyModules.Mutation

/--
info: 'AuditDependencyModules.cone_sound' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms AuditDependencyModules.cone_sound
/--
info: 'AuditDependencyModules.cone_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms AuditDependencyModules.cone_complete
/--
info: 'AuditDependencyModules.cone_affected' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms AuditDependencyModules.cone_affected
/--
info: 'AuditDependencyModules.closureHyp_is_inClosure' does not depend on any axioms
-/
#guard_msgs in
#print axioms AuditDependencyModules.closureHyp_is_inClosure
/--
info: 'AuditDependencyModules.coneGood_is_affected' does not depend on any axioms
-/
#guard_msgs in
#print axioms AuditDependencyModules.coneGood_is_affected
/--
info: 'AuditDependencyModules.same_profile_pareto' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms AuditDependencyModules.same_profile_pareto
/--
info: 'AuditDependencyModules.outputPoint_faithful' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms AuditDependencyModules.outputPoint_faithful
/--
info: 'AuditDependencyModules.Legacy.stringCone_iff_inClosure' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms AuditDependencyModules.Legacy.stringCone_iff_inClosure
/--
info: 'AuditDependencyModules.Legacy.stringCone_iff_affected' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms AuditDependencyModules.Legacy.stringCone_iff_affected
/--
info: 'AuditDependencyModules.Legacy.orderedCone_iff_affected' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms AuditDependencyModules.Legacy.orderedCone_iff_affected
/--
info: 'AuditDependencyModules.Mutation.mut_drop_hLoc' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms AuditDependencyModules.Mutation.mut_drop_hLoc
/--
info: 'AuditDependencyModules.Mutation.mut_drop_hOld' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms AuditDependencyModules.Mutation.mut_drop_hOld
