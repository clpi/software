import Family.Checker

/-!
# The checker always reaches closure

Closes the one open item of `Family.Checker`: `syms.length + 1` rounds of `stepK` always give a
closed set, as long as `syms` lists every symbol. Each round that is not yet closed adds at
least one new listed symbol, and there are only `syms.length` of them. With this, the incremental
verdict equals the whole-snapshot verdict with no closure side condition (`incr_eq_full'`), and
the computed set is exactly the cone (`coneK_eq_cone'`).
-/
namespace Family.Checker

open Family.Dataflow Family.Selection SoftwareIsIncrementallySafe.OrderedIncrement

variable {σ C β : Type} [DecidableEq σ]

def cnt (syms K : List σ) : Nat := syms.countP (fun s => decide (s ∈ K))

theorem cnt_le (syms K : List σ) : cnt syms K ≤ syms.length := List.countP_le_length

theorem cnt_mono (K K' : List σ) (hsub : ∀ x, x ∈ K → x ∈ K') :
    ∀ syms : List σ, cnt syms K ≤ cnt syms K'
  | [] => by simp [cnt]
  | x :: xs => by
    have ih := cnt_mono K K' hsub xs
    simp only [cnt, List.countP_cons] at ih ⊢
    by_cases hx : x ∈ K
    · have hx' := hsub x hx
      simp [hx, hx']; omega
    · by_cases hx' : x ∈ K'
      · simp [hx, hx']; omega
      · simp [hx, hx']; omega

theorem cnt_lt (K K' : List σ) (hsub : ∀ x, x ∈ K → x ∈ K') :
    ∀ syms : List σ, (∃ y, y ∈ syms ∧ y ∉ K ∧ y ∈ K') → cnt syms K < cnt syms K'
  | [], ⟨_, hy, _⟩ => by simp at hy
  | x :: xs, ⟨y, hy, hyK, hyK'⟩ => by
    rcases List.mem_cons.mp hy with rfl | hy
    · have := cnt_mono K K' hsub xs
      simp only [cnt, List.countP_cons] at this ⊢
      simp [hyK, hyK']; omega
    · have ih := cnt_lt K K' hsub xs ⟨y, hy, hyK, hyK'⟩
      simp only [cnt, List.countP_cons] at ih ⊢
      by_cases hx : x ∈ K
      · have hx' := hsub x hx
        simp [hx, hx']; omega
      · by_cases hx' : x ∈ K'
        · simp [hx, hx']; omega
        · simp [hx, hx']; omega

def ClosedD (deps : List (σ × σ)) (K : List σ) : Prop := ∀ e, e ∈ deps → e.2 ∈ K → e.1 ∈ K

theorem sub_stepK (deps : List (σ × σ)) (syms K : List σ) : ∀ x, x ∈ K → x ∈ stepK deps syms K :=
  fun _ hx => List.mem_append_left _ hx

theorem stepK_closed (deps : List (σ × σ)) (syms K : List σ) (h : ClosedD deps K) :
    stepK deps syms K = K := by
  unfold stepK
  have : syms.filter (fun s => !K.contains s && deps.any (fun e => e.1 == s && K.contains e.2))
      = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro s _ hs
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.any_eq_true, beq_iff_eq,
      List.contains_iff_mem] at hs
    obtain ⟨hsK, e, he, rfl, he2⟩ := hs
    have hm := h e he he2
    simp [hm] at hsK
  rw [this, List.append_nil]

theorem iterK_closed (deps : List (σ × σ)) (syms : List σ) :
    ∀ n K, ClosedD deps K → iterK deps syms n K = K
  | 0, _, _ => rfl
  | n + 1, K, h => by simp only [iterK, stepK_closed deps syms K h]; exact iterK_closed deps syms n K h

theorem stepK_grows (deps : List (σ × σ)) (syms K : List σ) (hsyms : ∀ s, s ∈ syms)
    (h : ¬ ClosedD deps K) : cnt syms K < cnt syms (stepK deps syms K) := by
  apply cnt_lt K _ (sub_stepK deps syms K)
  have hex : ∃ e, e ∈ deps ∧ e.2 ∈ K ∧ e.1 ∉ K := by
    apply Classical.byContradiction
    intro hn
    apply h
    intro e he he2
    apply Classical.byContradiction
    intro h1
    exact hn ⟨e, he, he2, h1⟩
  obtain ⟨e, he, he2, he1⟩ := hex
  refine ⟨e.1, hsyms _, he1, List.mem_append_right _ ?_⟩
  simp only [List.mem_filter, Bool.and_eq_true, Bool.not_eq_true', List.any_eq_true, beq_iff_eq,
    List.contains_iff_mem]
  exact ⟨hsyms _, by simpa using he1, e, he, rfl, he2⟩

theorem iterK_progress (deps : List (σ × σ)) (syms : List σ) (hsyms : ∀ s, s ∈ syms) :
    ∀ n K, ClosedD deps (iterK deps syms n K) ∨ n + cnt syms K ≤ cnt syms (iterK deps syms n K)
  | 0, K => Or.inr (by simp [iterK])
  | n + 1, K => by
    by_cases hK : ClosedD deps K
    · left; rw [iterK_closed deps syms _ K hK]; exact hK
    · have hg := stepK_grows deps syms K hsyms hK
      rcases iterK_progress deps syms hsyms n (stepK deps syms K) with h | h
      · left; simpa [iterK] using h
      · right; simp only [iterK]; omega

theorem iterK_sub (deps : List (σ × σ)) (syms : List σ) :
    ∀ n K x, x ∈ K → x ∈ iterK deps syms n K
  | 0, _, _, hx => hx
  | n + 1, K, x, hx => iterK_sub deps syms n _ x (sub_stepK deps syms K x hx)

theorem coneK_closed (deps : List (σ × σ)) (syms changed : List σ) (hsyms : ∀ s, s ∈ syms) :
    closedB deps changed (coneK deps syms changed) = true := by
  have hcl : ClosedD deps (coneK deps syms changed) := by
    rcases iterK_progress deps syms hsyms (syms.length + 1) changed with h | h
    · exact h
    · have := cnt_le syms (iterK deps syms (syms.length + 1) changed)
      unfold coneK; omega
  simp only [closedB, Bool.and_eq_true, List.all_eq_true]
  refine ⟨fun c hc => ?_, fun e he => ?_⟩
  · simpa using iterK_sub deps syms _ changed c hc
  · by_cases h2 : e.2 ∈ coneK deps syms changed
    · simp [hcl e he h2]
    · simp [h2]

/-- The incremental verdict is the whole-snapshot verdict, unconditionally. -/
theorem incr_eq_full' (deps : List (σ × σ)) (syms changed : List σ) (hsyms : ∀ s, s ∈ syms)
    (chk : σ → β → Bool) (sem : (σ → C) → σ → β) (I new : σ → C)
    (hLoc : Local (DepsL deps) sem) (hOld : ∀ s, chk s (sem I s) = true) :
    incrCheck deps syms changed chk sem I new = fullCheck syms changed chk sem I new :=
  incr_eq_full deps syms changed hsyms chk sem I new hLoc hOld
    (coneK_closed deps syms changed hsyms)

/-- The computed recheck set is exactly the cone. -/
theorem coneK_eq_cone' (deps : List (σ × σ)) (syms changed : List σ) (hsyms : ∀ s, s ∈ syms)
    (s : σ) : s ∈ coneK deps syms changed ↔ Cone (DepsL deps) (chOf changed) s :=
  coneK_eq_cone deps syms changed (coneK_closed deps syms changed hsyms) s

end Family.Checker
