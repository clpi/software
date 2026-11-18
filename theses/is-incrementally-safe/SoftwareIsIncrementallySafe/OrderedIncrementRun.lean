import SoftwareIsIncrementallySafe.OrderedIncrement
import SoftwareIsIncrementallySafe.RunAdmission
import SoftwareIsIncrementallySafe.AuditFix

/-!
# Executable incremental checker over `RunAdmission`

Sections 5 and 6 of the ordered incremental development: an executable check
over the existing finite run model, sound for the whole release by
`OrderedIncrement.recheck_iff_scratch`, and the two audit counterexamples
rerun against it.
-/

namespace SoftwareIsIncrementallySafe.OrderedIncrement

open Classical

/-! ## 5. Executable incremental checker over `RunAdmission`

The cone is an untrusted witness `K`. The checker verifies that `K` is closed
(contains every changed symbol and every dependent of a member), then runs the
existing ordered-trace and relational check on the members of `K` only. A
closed `K` contains the whole cone, so the result holds for the whole release.
This also removes the gap where a computed cone was proven sound but not
complete: completeness is checked, not assumed. -/

open RunAdmission

def listDeps (deps : List (String × String)) : String → String → Prop :=
  fun a b => (a, b) ∈ deps

def changedOf (changed : List String) : String → Bool :=
  fun s => changed.contains s

def ClosedCone (deps : List (String × String)) (changed K : List String) : Prop :=
  (∀ s ∈ changed, s ∈ K) ∧ (∀ p ∈ deps, p.2 ∈ K → p.1 ∈ K)

instance (deps : List (String × String)) (changed K : List String) :
    Decidable (ClosedCone deps changed K) := by
  unfold ClosedCone
  infer_instance

def incrCheck (pol : String → Policy) (deps : List (String × String))
    (changed K : List String) (models : String → Model) : Bool :=
  decide (ClosedCone deps changed K) && K.all (fun s => RunAdmission.check (pol s) (models s))

theorem closed_contains_cone {deps : List (String × String)} {changed K : List String}
    (h : ClosedCone deps changed K) {s : String}
    (hc : Cone (listDeps deps) (changedOf changed) s) : s ∈ K := by
  induction hc with
  | root hr =>
    apply h.1
    simpa [changedOf] using hr
  | step hd _ ih => exact h.2 _ hd ih

/-- HEADLINE (executable). With a sound graph and an accepted old release, if the
incremental checker accepts the change, every symbol of the new release passes
`RunAdmission.check`: ordered-trace safety, required runs, and two-run
noninterference. -/
theorem incrCheck_sound {C : Type} (pol : String → Policy) (deps : List (String × String))
    (sem : (String → C) → String → Model) (I new : String → C) (changed K : List String)
    (hLoc : Local (listDeps deps) sem)
    (hOld : ∀ s, RunAdmission.check (pol s) (sem I s) = true)
    (hAcc : incrCheck pol deps changed K (sem (update I (changedOf changed) new)) = true) :
    ∀ s, RunAdmission.check (pol s) (sem (update I (changedOf changed) new) s) = true := by
  simp only [incrCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hAcc
  obtain ⟨hClosed, hAll⟩ := hAcc
  exact (recheck_iff_scratch (listDeps deps) sem (fun s m => RunAdmission.check (pol s) m = true)
    I (changedOf changed) new hLoc hOld).mp
    (fun s hc => hAll s (closed_contains_cone hClosed hc))

theorem incr_accepted_ordered {C : Type} (pol : String → Policy) (deps : List (String × String))
    (sem : (String → C) → String → Model) (I new : String → C) (changed K : List String)
    (hLoc : Local (listDeps deps) sem)
    (hOld : ∀ s, RunAdmission.check (pol s) (sem I s) = true)
    (hAcc : incrCheck pol deps changed K (sem (update I (changedOf changed) new)) = true)
    (s : String) :
    ∀ i ∈ (pol s).inputs, ∀ t ∈ (sem (update I (changedOf changed) new) s).runs i,
      (pol s).traceAllowed i t = true :=
  accepted_ordered_traces _ _ (incrCheck_sound pol deps sem I new changed K hLoc hOld hAcc s)

theorem incr_accepted_relational {C : Type} (pol : String → Policy)
    (deps : List (String × String))
    (sem : (String → C) → String → Model) (I new : String → C) (changed K : List String)
    (hLoc : Local (listDeps deps) sem)
    (hOld : ∀ s, RunAdmission.check (pol s) (sem I s) = true)
    (hAcc : incrCheck pol deps changed K (sem (update I (changedOf changed) new)) = true)
    (s i j : String) (hi : i ∈ (pol s).inputs) (hj : j ∈ (pol s).inputs)
    (he : (pol s).lowEq i j = true) :
    ∀ t, t ∈ outputs (pol s) (sem (update I (changedOf changed) new) s) i ↔
      t ∈ outputs (pol s) (sem (update I (changedOf changed) new) s) j :=
  accepted_relational _ _ (incrCheck_sound pol deps sem I new changed K hLoc hOld hAcc s)
    i j hi hj he

/-! ## 6. The two audit counterexamples, rerun -/

/-- `dst` replays `src`'s runs. -/
def pass (src dst : String) : (String → Model) → String → Model :=
  fun I s => if s = dst then I src else I s

theorem pass_local (src dst : String) : Local (listDeps [(dst, src)]) (pass src dst) := by
  intro I I' s h
  unfold pass
  by_cases hs : s = dst
  · subst hs
    simp only [if_true]
    exact h src (DepStar.step (by simp [listDeps]) (DepStar.refl _))
  · simp only [hs, if_false]
    exact h s (DepStar.refl _)

/-! ### C5: order. `door` replays `sensor`; its policy is "never open before stop". -/

/-- `noOpenBeforeStop` from `RunAdmission` is a safety property: prefix-closed. -/
theorem noOpenBeforeStop_prefix (b : Bool) (p r : List String) :
    noOpenBeforeStop b (p ++ r) = true → noOpenBeforeStop b p = true := by
  induction p generalizing b with
  | nil => intro _; rfl
  | cons e es ih =>
    intro h
    simp only [List.cons_append, noOpenBeforeStop] at h ⊢
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

theorem noOpenBeforeStop_prefixClosed :
    PrefixClosed (fun t : List String => noOpenBeforeStop false t = true) := by
  intro t p ht ⟨r, hr⟩
  subst hr
  exact noOpenBeforeStop_prefix false p r ht

def anyPolicy : Policy := { trainPolicy with traceAllowed := fun _ _ => true }

def doorPol : String → Policy := fun s => if s = "door" then trainPolicy else anyPolicy

def sensorOld : String → Model := fun _ => ⟨fun _ => [["stop", "open"]]⟩
def sensorReordered : String → Model := fun _ => ⟨fun _ => [["open", "stop"]]⟩

def doorDeps : List (String × String) := [("door", "sensor")]
def doorSem := pass "sensor" "door"

/-- Same multiset of events, opposite order: the reordered change is refused. -/
theorem reordered_refused :
    incrCheck doorPol doorDeps ["sensor"] ["sensor", "door"]
      (doorSem (update sensorOld (changedOf ["sensor"]) sensorReordered)) = false := by
  decide

/-- An incomplete cone witness is refused before any model is checked. -/
theorem incomplete_witness_refused :
    incrCheck doorPol doorDeps ["sensor"] ["sensor"]
      (doorSem (update sensorOld (changedOf ["sensor"]) sensorReordered)) = false := by
  decide

/-- The correctly ordered change is accepted. -/
def sensorRetimed : String → Model := fun _ => ⟨fun _ => [["stop", "wait", "open"]]⟩

theorem ordered_accepted :
    incrCheck doorPol doorDeps ["sensor"] ["sensor", "door"]
      (doorSem (update sensorOld (changedOf ["sensor"]) sensorRetimed)) = true := by
  decide

/-- The old allow-list predicate cannot tell the two orders apart. -/
theorem allowList_blind (A : String → Prop) :
    allowedTrace A ["open", "stop"] ↔ allowedTrace A ["stop", "open"] :=
  allow_list_ignores_order A "open" "stop"

/-! ### C6: flow. `app` replays `lib`; `lib`'s own view is internal. -/

def libPolicy : Policy := { secretPolicy with lowView := fun _ => [] }
def flowPol : String → Policy := fun s => if s = "app" then secretPolicy else libPolicy

def libOld : String → Model := fun _ => noisy
def libLeaking : String → Model := fun _ => leaking

def flowDeps : List (String × String) := [("app", "lib")]
def flowSem := pass "lib" "app"

/-- Checking `lib` alone passes: its own view reveals nothing. -/
theorem lib_alone_passes : RunAdmission.check libPolicy leaking = true := by decide

/-- The incremental checker refuses the leak through `app`. -/
theorem leak_refused :
    incrCheck flowPol flowDeps ["lib"] ["lib", "app"]
      (flowSem (update libOld (changedOf ["lib"]) libLeaking)) = false := by
  decide

/-- Dropping `app` from the witness is caught by the closure check. -/
theorem leak_incomplete_witness_refused :
    incrCheck flowPol flowDeps ["lib"] ["lib"]
      (flowSem (update libOld (changedOf ["lib"]) libLeaking)) = false := by
  decide

/-- The two models have the same set of observed events, which is all the old
profile-based `NI` could see. -/
theorem same_observations (o : String) :
    (∃ i t, t ∈ leaking.runs i ∧ o ∈ t ∧ i ∈ secretPolicy.inputs) ↔
      (∃ i t, t ∈ noisy.runs i ∧ o ∈ t ∧ i ∈ secretPolicy.inputs) := by
  constructor
  · rintro ⟨i, t, ht, ho, hi⟩
    simp only [leaking, List.mem_singleton] at ht
    subst ht
    exact ⟨i, [i], by simp [noisy, secretPolicy] at hi ⊢; exact hi, ho, hi⟩
  · rintro ⟨i, t, ht, ho, hi⟩
    simp only [noisy, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact ⟨"0", ["0"], by simp [leaking], ho, by simp [secretPolicy]⟩
    · exact ⟨"1", ["1"], by simp [leaking], ho, by simp [secretPolicy]⟩

/-- The abstract version of the same pair: equal event sets, different NI verdicts. -/
theorem same_events_abstract (o : Bool) :
    (∃ i t, leak i t ∧ o ∈ t) ↔ (∃ i t, noise i t ∧ o ∈ t) := by
  constructor
  · intro _
    exact ⟨o, [o], by cases o <;> simp [noise], by simp⟩
  · intro _
    exact ⟨o, [o], rfl, by simp⟩

end SoftwareIsIncrementallySafe.OrderedIncrement

#print axioms SoftwareIsIncrementallySafe.OrderedIncrement.incrCheck_sound
#print axioms SoftwareIsIncrementallySafe.OrderedIncrement.reordered_refused
#print axioms SoftwareIsIncrementallySafe.OrderedIncrement.leak_refused
#print axioms SoftwareIsIncrementallySafe.OrderedIncrement.noOpenBeforeStop_prefixClosed
