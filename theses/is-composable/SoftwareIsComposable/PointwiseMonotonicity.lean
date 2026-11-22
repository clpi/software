namespace SoftwareIsComposable
namespace PointwiseModel

structure Profile (Observation : Type) where
  observes : Observation → Prop

def profileLE {Observation : Type} (new old : Profile Observation) : Prop :=
  ∀ observation, new.observes observation → old.observes observation

theorem profileLE_refl {Observation : Type} (profile : Profile Observation) :
    profileLE profile profile :=
  fun _ proof => proof

theorem profileLE_trans {Observation : Type} {a b c : Profile Observation}
    (hab : profileLE a b) (hbc : profileLE b c) : profileLE a c :=
  fun observation proof => hbc observation (hab observation proof)

structure Release (Symbol Observation : Type) where
  behavior : Symbol → Profile Observation

def releaseLE {Symbol Observation : Type}
    (new old : Release Symbol Observation) : Prop :=
  ∀ symbol, profileLE (new.behavior symbol) (old.behavior symbol)

structure Delta (Symbol Observation : Type) where
  changed : Symbol → Bool
  update : Symbol → Profile Observation
  inspect : Symbol → Bool

def apply {Symbol Observation : Type}
    (release : Release Symbol Observation) (delta : Delta Symbol Observation) :
    Release Symbol Observation where
  behavior symbol :=
    if delta.changed symbol then delta.update symbol else release.behavior symbol

theorem apply_changed {Symbol Observation : Type}
    (release : Release Symbol Observation) (delta : Delta Symbol Observation)
    {symbol : Symbol} (changed : delta.changed symbol = true) :
    (apply release delta).behavior symbol = delta.update symbol := by
  simp [apply, changed]

theorem apply_unchanged {Symbol Observation : Type}
    (release : Release Symbol Observation) (delta : Delta Symbol Observation)
    {symbol : Symbol} (unchanged : delta.changed symbol = false) :
    (apply release delta).behavior symbol = release.behavior symbol := by
  simp [apply, unchanged]

theorem incremental_monotone {Symbol Observation : Type}
    (release : Release Symbol Observation) (delta : Delta Symbol Observation)
    (changedProfilesShrink : ∀ symbol, delta.changed symbol = true →
      profileLE (delta.update symbol) (release.behavior symbol)) :
    releaseLE (apply release delta) release := by
  intro symbol
  cases hchanged : delta.changed symbol with
  | true =>
    rw [apply_changed release delta hchanged]
    exact changedProfilesShrink symbol hchanged
  | false =>
    rw [apply_unchanged release delta hchanged]
    exact profileLE_refl _

end PointwiseModel
end SoftwareIsComposable
