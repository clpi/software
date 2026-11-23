import SoftwareIsComposable.Interaction

namespace SoftwareIsComposable.InteractionControls

open Legacy

inductive Observation where
  | a | b | alarm
  deriving DecidableEq

def expected (component : Bool) : Observation :=
  if component then .b else .a

def seeds (component : Bool) : Profile Observation :=
  ⟨fun o => o = expected component⟩

def allowed (o : Observation) : Prop := o ≠ .alarm

def noDeps (_s _t : Bool) : Prop := False

def composedDeps (s t : Bool) : Prop := s = false ∧ t = true

def joint : Interaction.Join Observation :=
  fun x y z => x = .a ∧ y = .b ∧ z = .alarm

theorem isolated_has_only_own_observation {s : Bool} {o : Observation}
    (h : Interaction.Reaches noDeps joint seeds s o) : o = expected s := by
  induction h with
  | here hobs => exact hobs
  | step hdep _ _ => exact hdep.elim
  | interact hjoin _ _ ha hb =>
    rcases hjoin with ⟨rfl, rfl, rfl⟩
    cases ha.trans hb.symm

theorem isolated_components_are_safe :
    Interaction.Safe noDeps joint seeds allowed := by
  intro s o h
  have heq := isolated_has_only_own_observation h
  cases heq
  intro bad
  cases s <;> cases bad

theorem seed_profiles_are_safe : Interaction.LocallySafe seeds allowed :=
  fun s o ho => isolated_components_are_safe s o (.here ho)

theorem composed_alarm :
    Interaction.Reaches composedDeps joint seeds false .alarm :=
  .interact ⟨rfl, rfl, rfl⟩ (.here rfl) (.step ⟨rfl, rfl⟩ (.here rfl))

theorem composition_of_isolated_safe_components_is_unsafe :
    Interaction.Safe noDeps joint seeds allowed ∧
      ¬ Interaction.Safe composedDeps joint seeds allowed := by
  refine ⟨isolated_components_are_safe, ?_⟩
  intro h
  exact h false .alarm composed_alarm rfl

theorem alarm_has_no_component_origin : ∀ s, ¬ (seeds s).obs .alarm := by
  intro s h
  cases s <;> cases h

theorem legacy_composition_cannot_derive_alarm :
    ¬ Legacy.Reaches composedDeps seeds false .alarm := by
  intro h
  rcases Interaction.legacy_has_origin h with ⟨s, ho⟩
  exact alarm_has_no_component_origin s ho

theorem allowed_is_not_interaction_closed : ¬ Interaction.JoinClosed joint allowed := by
  intro h
  have ha : allowed .a := by intro h; cases h
  have hb : allowed .b := by intro h; cases h
  exact h .a .b .alarm ⟨rfl, rfl, rfl⟩ ha hb rfl

theorem topology_change_breaks_global_refinement :
    (∀ s, profileLE (seeds s) (seeds s)) ∧
      ¬ (∀ s o, Interaction.Reaches composedDeps joint seeds s o →
        Interaction.Reaches noDeps joint seeds s o) := by
  refine ⟨fun _ _ h => h, ?_⟩
  intro h
  have impossible := isolated_has_only_own_observation (h false .alarm composed_alarm)
  cases impossible

def noRules : Interaction.Join Observation := fun _ _ _ => False

theorem rule_change_breaks_global_refinement :
    (∀ s, profileLE (seeds s) (seeds s)) ∧
      ¬ (∀ s o, Interaction.Reaches composedDeps joint seeds s o →
        Interaction.Reaches composedDeps noRules seeds s o) := by
  refine ⟨fun _ _ h => h, ?_⟩
  intro h
  exact legacy_composition_cannot_derive_alarm
    (Interaction.no_interaction_iff_legacy.mp (h false .alarm composed_alarm))

def shrunkSeeds (component : Bool) : Profile Observation :=
  ⟨fun o => component = false ∧ o = .a⟩

def emptySeeds : Bool → Profile Observation := fun _ => ⟨fun _ => False⟩

theorem strict_local_refinement :
    (∀ s, profileLE (shrunkSeeds s) (seeds s)) ∧
      ¬ (∀ s, profileLE (seeds s) (shrunkSeeds s)) := by
  constructor
  · intro s o ho
    rcases ho with ⟨rfl, rfl⟩
    rfl
  · intro h
    have impossible := (h true .b rfl).1
    cases impossible

theorem positive_interaction_refinement_survives :
    ∀ s o, Interaction.Reaches composedDeps joint shrunkSeeds s o →
      Interaction.Reaches composedDeps joint seeds s o :=
  fun _ _ h => Interaction.reaches_monotone strict_local_refinement.1 h

theorem empty_seeds_do_not_bootstrap
    {σ ω : Type} (deps : σ → σ → Prop) (join : Interaction.Join ω)
    {s : σ} {o : ω} :
    ¬ Interaction.Reaches deps join (fun _ => ⟨fun _ => False⟩) s o := by
  intro h
  induction h with
  | here hobs => exact hobs
  | step _ _ ih => exact ih
  | interact _ _ _ ih _ => exact ih

def cyclicRules : Interaction.Join Observation :=
  fun x y z => x = .alarm ∧ y = .alarm ∧ z = .alarm

theorem positive_cycle_cannot_self_justify :
    ¬ Interaction.Reaches noDeps cyclicRules emptySeeds false .alarm :=
  empty_seeds_do_not_bootstrap noDeps cyclicRules


theorem positive_refinement_has_live_observation :
    Interaction.Reaches composedDeps joint shrunkSeeds false .a :=
  .here ⟨rfl, rfl⟩

theorem shrunk_closure_has_only_a {s : Bool} {o : Observation}
    (h : Interaction.Reaches composedDeps joint shrunkSeeds s o) : o = .a := by
  induction h with
  | here hobs => exact hobs.2
  | step _ _ ih => exact ih
  | interact hrule _ _ _ hb =>
    rcases hrule with ⟨rfl, rfl, rfl⟩
    cases hb

theorem positive_refinement_removes_alarm :
    ¬ Interaction.Reaches composedDeps joint shrunkSeeds false .alarm := by
  intro h
  cases shrunk_closure_has_only_a h

def chainRules : Interaction.Join Observation := fun x y z =>
  (x = .a ∧ y = .a ∧ z = .b) ∨ (x = .b ∧ y = .b ∧ z = .alarm)

def shortcutRules : Interaction.Join Observation := fun x y z =>
  chainRules x y z ∨ (x = .a ∧ y = .a ∧ z = .alarm)

theorem shortcut_is_not_rule_subset : ¬ Interaction.JoinLE shortcutRules chainRules := by
  intro h
  have hrule := h (a := .a) (b := .a) (c := .alarm) (Or.inr ⟨rfl, rfl, rfl⟩)
  rcases hrule with ⟨_, _, hz⟩ | ⟨hx, _, _⟩
  · cases hz
  · cases hx

theorem shortcut_primitive_simulated {σ : Type} {deps : σ → σ → Prop}
    {B : σ → Profile Observation} {s : σ} {x y z : Observation}
    (hrule : shortcutRules x y z)
    (hx : Interaction.Reaches deps chainRules B s x)
    (hy : Interaction.Reaches deps chainRules B s y) :
    Interaction.Reaches deps chainRules B s z := by
  rcases hrule with hrule | ⟨rfl, rfl, rfl⟩
  · exact .interact hrule hx hy
  · have mid : Interaction.Reaches deps chainRules B s .b :=
      .interact (Or.inl ⟨rfl, rfl, rfl⟩) hx hy
    exact .interact (Or.inr ⟨rfl, rfl, rfl⟩) mid mid

theorem shortcut_extension_preserves_closure {σ : Type} (deps : σ → σ → Prop)
    (B : σ → Profile Observation) (s : σ) (o : Observation) :
    Interaction.Reaches deps shortcutRules B s o ↔
      Interaction.Reaches deps chainRules B s o := by
  constructor
  · exact Interaction.reaches_simulation
      (fun _ _ ho => .here ho)
      (fun _ _ _ hd ho => .step hd ho)
      (fun _ _ _ _ hj hx hy => shortcut_primitive_simulated hj hx hy)
  · exact Interaction.reaches_refinement
      (fun {_ _} h => h) (fun {_ _ _} h => Or.inl h) (fun _ _ h => h)

theorem shortcut_has_live_witness :
    Interaction.Reaches noDeps shortcutRules seeds false .alarm :=
  .interact (Or.inr ⟨rfl, rfl, rfl⟩) (.here rfl) (.here rfl)

theorem primitive_join_obligation_is_load_bearing :
    (∀ s o, (seeds s).obs o → Interaction.Reaches composedDeps noRules seeds s o) ∧
    (∀ s t o, composedDeps s t → Interaction.Reaches composedDeps noRules seeds t o →
      Interaction.Reaches composedDeps noRules seeds s o) ∧
    ¬ (∀ s x y z, joint x y z →
      Interaction.Reaches composedDeps noRules seeds s x →
      Interaction.Reaches composedDeps noRules seeds s y →
      Interaction.Reaches composedDeps noRules seeds s z) := by
  refine ⟨fun _ _ h => .here h, fun _ _ _ hd ho => .step hd ho, ?_⟩
  intro h
  have impossible := h false .a .b .alarm ⟨rfl, rfl, rfl⟩
    (.here rfl) (.step ⟨rfl, rfl⟩ (.here rfl))
  exact legacy_composition_cannot_derive_alarm
    (Interaction.no_interaction_iff_legacy.mp impossible)

def fallback (p : Profile Observation) (o : Observation) : Prop :=
  p.obs o ∨ (o = .alarm ∧ ¬ p.obs .b)

def oldFallback : Profile Observation := ⟨fun o => o = .b⟩

def newFallback : Profile Observation := ⟨fun _ => False⟩

theorem absence_sensitive_refinement_fails :
    profileLE newFallback oldFallback ∧
      fallback newFallback .alarm ∧ ¬ fallback oldFallback .alarm := by
  refine ⟨fun _ h => h.elim, Or.inr ⟨rfl, fun h => h⟩, ?_⟩
  intro h
  rcases h with h | ⟨_, h⟩
  · cases h
  · exact h rfl

def emptySymbolSeeds : Empty → Profile Observation := Empty.elim

theorem no_root_makes_universal_safety_vacuous :
    (∀ B : Empty → Profile Observation,
      Interaction.LocallySafe B allowed →
        Interaction.Safe (fun _ _ => False) joint B allowed) ∧
      ¬ Interaction.JoinClosed joint allowed := by
  refine ⟨?_, allowed_is_not_interaction_closed⟩
  intro _ _ s
  exact Empty.elim s

end SoftwareIsComposable.InteractionControls
