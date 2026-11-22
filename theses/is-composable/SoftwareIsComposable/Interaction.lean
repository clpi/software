import SoftwareIsComposable.Legacy

namespace SoftwareIsComposable.Interaction

open Legacy

abbrev Join (ω : Type) := ω → ω → ω → Prop

def JoinLE {ω : Type} (new old : Join ω) : Prop :=
  ∀ ⦃a b c⦄, new a b c → old a b c

inductive Reaches {σ ω : Type} (deps : σ → σ → Prop) (join : Join ω)
    (B : σ → Profile ω) : σ → ω → Prop where
  | here {s : σ} {o : ω} : (B s).obs o → Reaches deps join B s o
  | step {s t : σ} {o : ω} :
      deps s t → Reaches deps join B t o → Reaches deps join B s o
  | interact {s : σ} {a b c : ω} :
      join a b c → Reaches deps join B s a → Reaches deps join B s b →
      Reaches deps join B s c

def LocallySafe {σ ω : Type} (B : σ → Profile ω) (allowed : ω → Prop) : Prop :=
  ∀ s o, (B s).obs o → allowed o

def Safe {σ ω : Type} (deps : σ → σ → Prop) (join : Join ω)
    (B : σ → Profile ω) (allowed : ω → Prop) : Prop :=
  ∀ s o, Reaches deps join B s o → allowed o

def JoinClosed {ω : Type} (join : Join ω) (allowed : ω → Prop) : Prop :=
  ∀ a b c, join a b c → allowed a → allowed b → allowed c

theorem incremental_monotone_iff {σ ω : Type} (R : Legacy.Release σ ω)
    (d : Delta σ ω) :
    releaseLE (Legacy.apply R d) R ↔
      ∀ s, d.changed s = true → profileLE (d.update s) (R.behavior s) := by
  constructor
  · intro h s hs
    have hlocal := h s
    rw [apply_changed R d hs] at hlocal
    exact hlocal
  · exact Legacy.incremental_monotone R d

theorem legacy_has_origin {σ ω : Type} {deps : σ → σ → Prop}
    {B : σ → Profile ω} {s : σ} {o : ω}
    (h : Legacy.Reaches deps B s o) : ∃ t, (B t).obs o := by
  induction h with
  | here hobs => exact ⟨_, hobs⟩
  | step _ _ ih => exact ih

theorem legacy_embeds {σ ω : Type} {deps : σ → σ → Prop} {join : Join ω}
    {B : σ → Profile ω} {s : σ} {o : ω}
    (h : Legacy.Reaches deps B s o) : Reaches deps join B s o := by
  induction h with
  | here hobs => exact .here hobs
  | step hdep _ ih => exact .step hdep ih

theorem no_interaction_iff_legacy {σ ω : Type} {deps : σ → σ → Prop}
    {B : σ → Profile ω} {s : σ} {o : ω} :
    Reaches deps (fun _ _ _ => False) B s o ↔ Legacy.Reaches deps B s o := by
  constructor
  · intro h
    induction h with
    | here hobs => exact .here hobs
    | step hdep _ ih => exact .step hdep ih
    | interact hjoin _ _ _ _ => exact hjoin.elim
  · exact legacy_embeds

theorem reaches_simulation {σ ω : Type} {newDeps oldDeps : σ → σ → Prop}
    {newJoin oldJoin : Join ω} {newB oldB : σ → Profile ω}
    (hbase : ∀ s o, (newB s).obs o → Reaches oldDeps oldJoin oldB s o)
    (hstep : ∀ s t o, newDeps s t →
      Reaches oldDeps oldJoin oldB t o → Reaches oldDeps oldJoin oldB s o)
    (hjoin : ∀ s a b c, newJoin a b c →
      Reaches oldDeps oldJoin oldB s a → Reaches oldDeps oldJoin oldB s b →
      Reaches oldDeps oldJoin oldB s c)
    {s : σ} {o : ω} (h : Reaches newDeps newJoin newB s o) :
    Reaches oldDeps oldJoin oldB s o := by
  induction h with
  | here hobs => exact hbase _ _ hobs
  | step hdep _ ih => exact hstep _ _ _ hdep ih
  | interact hrule _ _ ih1 ih2 => exact hjoin _ _ _ _ hrule ih1 ih2

theorem reaches_refinement {σ ω : Type} {newDeps oldDeps : σ → σ → Prop}
    {newJoin oldJoin : Join ω} {newB oldB : σ → Profile ω}
    (hdeps : ∀ ⦃s t⦄, newDeps s t → oldDeps s t)
    (hjoin : JoinLE newJoin oldJoin)
    (hbase : ∀ s, profileLE (newB s) (oldB s))
    {s : σ} {o : ω} (h : Reaches newDeps newJoin newB s o) :
    Reaches oldDeps oldJoin oldB s o :=
  reaches_simulation
    (fun s o ho => .here (hbase s o ho))
    (fun _ _ _ hd ho => .step (hdeps hd) ho)
    (fun _ _ _ _ hj ha hb => .interact (hjoin hj) ha hb) h

theorem reaches_monotone {σ ω : Type} {deps : σ → σ → Prop} {join : Join ω}
    {newB oldB : σ → Profile ω} (hbase : ∀ s, profileLE (newB s) (oldB s))
    {s : σ} {o : ω} (h : Reaches deps join newB s o) :
    Reaches deps join oldB s o :=
  reaches_refinement (fun {_ _} h => h) (fun {_ _ _} h => h) hbase h

theorem incremental_interactions_monotone {σ ω : Type} {deps : σ → σ → Prop}
    {join : Join ω} (R : Legacy.Release σ ω) (d : Delta σ ω)
    (hbase : ∀ s, d.changed s = true → profileLE (d.update s) (R.behavior s))
    {s : σ} {o : ω} (h : Reaches deps join (Legacy.apply R d).behavior s o) :
    Reaches deps join R.behavior s o :=
  reaches_monotone (Legacy.incremental_monotone R d hbase) h

theorem safe_of_closed {σ ω : Type} {deps : σ → σ → Prop} {join : Join ω}
    {B : σ → Profile ω} {allowed : ω → Prop}
    (hlocal : LocallySafe B allowed) (hclosed : JoinClosed join allowed) :
    Safe deps join B allowed := by
  intro s o h
  induction h with
  | here hobs => exact hlocal _ _ hobs
  | step _ _ ih => exact ih
  | interact hrule _ _ ih1 ih2 => exact hclosed _ _ _ hrule ih1 ih2

theorem universal_safety_iff_closed {σ ω : Type} (root : σ)
    (deps : σ → σ → Prop) (join : Join ω) (allowed : ω → Prop) :
    (∀ B : σ → Profile ω, LocallySafe B allowed → Safe deps join B allowed) ↔
      JoinClosed join allowed := by
  constructor
  · intro h a b c hrule ha hb
    let B : σ → Profile ω := fun _ => ⟨allowed⟩
    have hlocal : LocallySafe B allowed := fun _ _ hx => hx
    exact h B hlocal root c (.interact hrule (.here ha) (.here hb))
  · intro hclosed B hlocal
    exact safe_of_closed hlocal hclosed

theorem safe_of_simulation {σ ω : Type} {newDeps oldDeps : σ → σ → Prop}
    {newJoin oldJoin : Join ω} {newB oldB : σ → Profile ω} {allowed : ω → Prop}
    (hbase : ∀ s o, (newB s).obs o → Reaches oldDeps oldJoin oldB s o)
    (hstep : ∀ s t o, newDeps s t →
      Reaches oldDeps oldJoin oldB t o → Reaches oldDeps oldJoin oldB s o)
    (hjoin : ∀ s a b c, newJoin a b c →
      Reaches oldDeps oldJoin oldB s a → Reaches oldDeps oldJoin oldB s b →
      Reaches oldDeps oldJoin oldB s c)
    (hold : Safe oldDeps oldJoin oldB allowed) : Safe newDeps newJoin newB allowed :=
  fun s o h => hold s o (reaches_simulation hbase hstep hjoin h)

theorem safe_of_refinement {σ ω : Type} {newDeps oldDeps : σ → σ → Prop}
    {newJoin oldJoin : Join ω} {newB oldB : σ → Profile ω} {allowed : ω → Prop}
    (hdeps : ∀ ⦃s t⦄, newDeps s t → oldDeps s t)
    (hjoin : JoinLE newJoin oldJoin)
    (hbase : ∀ s, profileLE (newB s) (oldB s))
    (hold : Safe oldDeps oldJoin oldB allowed) :
    Safe newDeps newJoin newB allowed :=
  fun s o h => hold s o (reaches_refinement hdeps hjoin hbase h)

theorem safe_of_incremental {σ ω : Type} {deps : σ → σ → Prop} {join : Join ω}
    (R : Legacy.Release σ ω) (d : Delta σ ω) {allowed : ω → Prop}
    (hbase : ∀ s, d.changed s = true → profileLE (d.update s) (R.behavior s))
    (hold : Safe deps join R.behavior allowed) :
    Safe deps join (Legacy.apply R d).behavior allowed :=
  fun s o h => hold s o (incremental_interactions_monotone R d hbase h)

theorem reaches_transfer_outside {σ ω : Type} {deps : σ → σ → Prop}
    {join : Join ω} {changed : σ → Bool} {B B' : σ → Profile ω}
    (hagree : ∀ s, changed s = false → B' s = B s)
    {s : σ} {o : ω} (h : Reaches deps join B' s o)
    (hout : ¬ Cone deps changed s) : Reaches deps join B s o :=
  Reaches.rec
    (motive := fun s o _ => ¬ Cone deps changed s → Reaches deps join B s o)
    (fun {s o} hobs hout => by
      rw [hagree s (not_cone_not_changed hout)] at hobs
      exact .here hobs)
    (fun {_ _ _} hdep _ ih hout =>
      .step hdep (ih (fun ht => hout (.step hdep ht))))
    (fun {_ _ _ _} hrule _ _ ih1 ih2 hout => .interact hrule (ih1 hout) (ih2 hout))
    h hout

theorem reaches_outside_stable {σ ω : Type} {deps : σ → σ → Prop}
    {join : Join ω} {changed : σ → Bool} {B B' : σ → Profile ω}
    (hagree : ∀ s, changed s = false → B' s = B s)
    {s : σ} {o : ω} (hout : ¬ Cone deps changed s) :
    Reaches deps join B' s o ↔ Reaches deps join B s o :=
  ⟨fun h => reaches_transfer_outside hagree h hout,
   fun h => reaches_transfer_outside (fun s hs => (hagree s hs).symm) h hout⟩

theorem incremental_recheck_iff {σ ω : Type} {deps : σ → σ → Prop} {join : Join ω}
    (R : Legacy.Release σ ω) (d : Delta σ ω) {allowed : ω → Prop}
    (hold : Safe deps join R.behavior allowed) :
    Safe deps join (Legacy.apply R d).behavior allowed ↔
      ∀ s, Cone deps d.changed s →
        ∀ o, Reaches deps join (Legacy.apply R d).behavior s o → allowed o := by
  constructor
  · intro h s _ o ho
    exact h s o ho
  · intro h s o ho
    classical
    by_cases hc : Cone deps d.changed s
    · exact h s hc o ho
    · exact hold s o (reaches_transfer_outside (fun t ht => apply_unchanged R d ht) ho hc)

end SoftwareIsComposable.Interaction
