import SoftwareIsComposable
import SoftwareIsIncrementallyCertifiable

namespace SoftwareIsIncrementallySafe

open SoftwareIsComposable
open SoftwareIsIncrementallyCertifiable

abbrev Trace (ω : Type) := List ω

def IsSafetyProperty {ω : Type} (P : Profile ω → Prop) : Prop :=
  ∀ p, c P p → P p

theorem c_isSafetyProperty {ω : Type} (P : Profile ω → Prop) :
    IsSafetyProperty (c P) :=
  fun p hp => (c_idempotent P p).mp hp

theorem safetyProperty_iff_fixed {ω : Type} (P : Profile ω → Prop) :
    IsSafetyProperty P ↔ ∀ p, c P p ↔ P p := by
  constructor
  · intro hP p
    exact ⟨hP p, c_extensive P p⟩
  · intro h p hp
    exact (h p).mp hp

theorem safetyProperty_iff_downwardClosed {ω : Type} (P : Profile ω → Prop) :
    IsSafetyProperty P ↔ ∀ p q, P q → profileLE p q → P p := by
  constructor
  · intro hP p q hq hle
    exact hP p ⟨q, hq, hle⟩
  · intro h p ⟨q, hq, hle⟩
    exact h p q hq hle

def tracesOf {σ ω : Type} (R : Release σ ω) : Trace ω → Prop :=
  fun t => ∀ o, o ∈ t → ∃ s, (R.behavior s).obs o

def allowedTrace {ω : Type} (A : ω → Prop) : Trace ω → Prop :=
  fun t => ∀ o, o ∈ t → A o

theorem prefix_mem {α : Type} {p t : List α} {a : α}
    (hp : p <+: t) (ha : a ∈ p) : a ∈ t := by
  rcases hp with ⟨rest, rfl⟩
  exact (List.mem_append.mpr (Or.inl ha))

theorem allowedTraces_prefixClosed {ω : Type} (A : ω → Prop) {t p : Trace ω}
    (ht : allowedTrace A t) (hp : p <+: t) : allowedTrace A p :=
  fun o ho => ht o (prefix_mem hp ho)

theorem tracesOf_prefixClosed {σ ω : Type} (R : Release σ ω) {t p : Trace ω}
    (ht : tracesOf R t) (hp : p <+: t) : tracesOf R p :=
  fun o ho => ht o (prefix_mem hp ho)

def allowedProfile {ω : Type} (A : ω → Prop) : Profile ω → Prop :=
  fun p => ∀ o, p.obs o → A o

theorem allowedProfile_eq_c {ω : Type} (A : ω → Prop) (p : Profile ω) :
    c (allowedProfile A) p ↔ allowedProfile A p := by
  constructor
  · intro ⟨q, hq, hle⟩ o ho
    exact hq o (hle o ho)
  · intro hp
    exact c_extensive (allowedProfile A) p hp

theorem allowedProfile_safetyProperty {ω : Type} (A : ω → Prop) :
    IsSafetyProperty (allowedProfile A) :=
  fun p hp => (allowedProfile_eq_c A p).mp hp

theorem behaviorSafe_iff_traceSafe {σ ω : Type} (A : ω → Prop) (R : Release σ ω) :
    (∀ s, allowedProfile A (R.behavior s)) ↔
      (∀ t, tracesOf R t → allowedTrace A t) := by
  constructor
  · intro h t ht o ho
    rcases ht o ho with ⟨s, hs⟩
    exact h s o hs
  · intro h s o ho
    have ht : tracesOf R [o] := by
      intro o' ho'
      cases ho' with
      | head => exact ⟨s, ho⟩
      | tail _ hempty => exact (List.not_mem_nil hempty).elim
    exact h [o] ht o (List.Mem.head [])

theorem releaseSafe_iff_traceSafety {σ ω : Type} (A : ω → Prop) (R : Release σ ω) :
    (∀ s, c (allowedProfile A) (R.behavior s)) ↔
      (∀ t, tracesOf R t → allowedTrace A t) := by
  constructor
  · intro h
    exact (behaviorSafe_iff_traceSafe A R).mp
      (fun s => (allowedProfile_eq_c A (R.behavior s)).mp (h s))
  · intro h s
    exact (allowedProfile_eq_c A (R.behavior s)).mpr
      ((behaviorSafe_iff_traceSafe A R).mpr h s)

theorem safe_downward {σ ω : Type} {P : Profile ω → Prop}
    (hP : IsSafetyProperty P) {R R' : Release σ ω}
    (hR : ∀ s, P (R.behavior s)) (hle : releaseLE R' R) :
    ∀ s, P (R'.behavior s) :=
  fun s => hP (R'.behavior s) ⟨R.behavior s, hR s, hle s⟩

structure UpstreamExport (ω : Type) where
  closure : (Profile ω → Prop) → Profile ω → Prop
  order : Profile ω → Profile ω → Prop
  pareto : Cost → Cost → Prop
  closure_agrees : ∀ P p, closure P p ↔ c P p
  order_agrees : ∀ p q, order p q ↔ profileLE p q
  pareto_agrees : ∀ a b, pareto a b ↔ paretoLE a b

def canonicalUpstream {ω : Type} : UpstreamExport ω where
  closure := c
  order := profileLE
  pareto := paretoLE
  closure_agrees := fun _ _ => Iff.rfl
  order_agrees := fun _ _ => Iff.rfl
  pareto_agrees := fun _ _ => Iff.rfl

theorem equivalence_obligation_upstream {ω : Type}
    (P : Profile ω → Prop) (p q : Profile ω) (a b : Cost) :
    ((canonicalUpstream (ω := ω)).closure P p ↔ c P p) ∧
    ((canonicalUpstream (ω := ω)).order p q ↔ profileLE p q) ∧
    ((canonicalUpstream (ω := ω)).pareto a b ↔ paretoLE a b) :=
  ⟨Iff.rfl, Iff.rfl, Iff.rfl⟩

theorem isSafety_transport {ω : Type} (E : UpstreamExport ω) (P : Profile ω → Prop)
    (h : ∀ p, E.closure P p → P p) : IsSafetyProperty P :=
  fun p hp => h p ((E.closure_agrees P p).mpr hp)

end SoftwareIsIncrementallySafe
