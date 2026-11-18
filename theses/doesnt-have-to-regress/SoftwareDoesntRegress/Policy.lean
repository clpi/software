import SoftwareDoesntRegress.Gate

namespace SoftwareDoesntRegress

theorem ascend_cons {β : Type} [DecidableEq β] (acc c : Release β) (cs : List (Release β)) :
    ascend acc (c :: cs) = ascend (step acc c) cs := by
  simp [ascend, List.foldl_cons]

theorem ascend_noRegress {β : Type} [DecidableEq β] (acc : Release β) (U : List (Release β)) :
    noRegress acc (ascend acc U) = true := by
  induction U generalizing acc with
  | nil => simp [ascend, List.foldl_nil, noRegress_refl]
  | cons c cs ih =>
    rw [ascend_cons]
    exact noRegress_trans (step_noRegress acc c) (ih _)

theorem ascendFuel_zero {β : Type} [DecidableEq β] (acc : Release β) (U : List (Release β)) :
    ascendFuel 0 acc U = acc := by
  simp [ascendFuel]

theorem ascendFuel_succ_nil {β : Type} [DecidableEq β] (n : Nat) (acc : Release β) :
    ascendFuel (n + 1) acc [] = acc := by
  simp [ascendFuel]

theorem ascendFuel_succ_cons {β : Type} [DecidableEq β] (n : Nat) (acc c : Release β)
    (cs : List (Release β)) :
    ascendFuel (n + 1) acc (c :: cs) = ascendFuel n (step acc c) cs := by
  simp [ascendFuel]

theorem ascend_fuel {β : Type} [DecidableEq β] (acc : Release β) (U : List (Release β)) :
    ascend acc U = ascendFuel U.length acc U := by
  induction U generalizing acc with
  | nil => simp [ascend, List.foldl_nil, ascendFuel]
  | cons c cs ih =>
    rw [ascend_cons, List.length_cons, ascendFuel_succ_cons]
    exact ih _

theorem step_accepts {β : Type} [DecidableEq β] {inc cand : Release β}
    (h : accepts inc cand = true) : step inc cand = cand := by
  simp [step, h]

theorem step_refuses {β : Type} [DecidableEq β] {inc cand : Release β}
    (h : accepts inc cand = false) : step inc cand = inc := by
  simp [step, h]

theorem accepts_ok_inc {β : Type} [DecidableEq β] {inc cand : Release β}
    (h : accepts inc cand = true) : releaseOk inc = true :=
  (accepts_iff_parts (inc := inc) (cand := cand)).mp h |>.1

theorem accepts_noRegress_of {β : Type} [DecidableEq β] {inc cand : Release β}
    (h : accepts inc cand = true) : noRegress inc cand = true :=
  (accepts_iff_parts (inc := inc) (cand := cand)).mp h |>.2.2.1

theorem ascend_stuck {β : Type} [DecidableEq β] {acc : Release β} (U : List (Release β))
    (h : releaseOk acc = false) : ascend acc U = acc := by
  induction U generalizing acc with
  | nil => simp [ascend, List.foldl_nil]
  | cons c cs ih =>
    have hacc : accepts acc c = false := by
      cases hacc : accepts acc c with
      | false => rfl
      | true =>
        have hok := accepts_ok_inc hacc
        simp [hok] at h
    rw [ascend_cons, step_refuses hacc]
    exact ih h

theorem ascend_maximal {β : Type} [DecidableEq β] (acc : Release β) (U : List (Release β)) :
    ∀ c ∈ U, accepts (ascend acc U) c = false := by
  induction U generalizing acc with
  | nil =>
    intro c hc
    cases hc
  | cons head tail ih =>
    intro c hc
    rw [ascend_cons]
    cases hc with
    | head =>
      cases hok : releaseOk acc with
      | false =>
        have hacc : accepts acc head = false := by
          cases htry : accepts acc head with
          | false => rfl
          | true =>
            have := accepts_ok_inc htry
            simp [this] at hok
        rw [step_refuses hacc, ascend_stuck tail hok]
        exact hacc
      | true =>
        cases hacc : accepts acc head with
        | true =>
          rw [step_accepts hacc]
          have hdesc := ascend_noRegress head tail
          cases hout : accepts (ascend head tail) head with
          | false => rfl
          | true =>
            have hback := accepts_noRegress_of hout
            have hstrict := strictGain_of_antisym hback hdesc
            have hs := (accepts_iff_parts (inc := ascend head tail) (cand := head)).mp hout
            simp [hstrict] at hs
        | false =>
          rw [step_refuses hacc]
          have hdesc := ascend_noRegress acc tail
          cases hout : accepts (ascend acc tail) head with
          | false => rfl
          | true =>
            have hlift := accepts_lift hdesc hout hok
            simp [hlift] at hacc
    | tail _ hmem =>
      exact ih (step acc head) c hmem

theorem ascend_ships {β : Type} [DecidableEq β] {inc acc : Release β} {U : List (Release β)}
    (hrel : noRegress inc acc = true)
    (hmove : acc = inc ∨ accepts inc acc = true)
    (hprog : accepts inc acc = true ∨ ∃ c, c ∈ U ∧ accepts inc c = true) :
    accepts inc (ascend acc U) = true := by
  induction U generalizing acc with
  | nil =>
    cases hprog with
    | inl h => simpa [ascend, List.foldl_nil] using h
    | inr h =>
      obtain ⟨_, hc, _⟩ := h
      cases hc
  | cons c cs ih =>
    rw [ascend_cons]
    cases hacc : accepts acc c with
    | true =>
      have hok : releaseOk inc = true := by
        cases hmove with
        | inl heq =>
          cases heq
          exact accepts_ok_inc hacc
        | inr h => exact accepts_ok_inc h
      rw [step_accepts hacc]
      apply ih
      · exact noRegress_trans hrel (accepts_noRegress_of hacc)
      · exact Or.inr (accepts_lift hrel hacc hok)
      · exact Or.inl (accepts_lift hrel hacc hok)
    | false =>
      rw [step_refuses hacc]
      apply ih hrel hmove
      cases hprog with
      | inl h => exact Or.inl h
      | inr hex =>
        obtain ⟨d, hd, had⟩ := hex
        cases hd with
        | head =>
          cases hmove with
          | inl heq =>
            cases heq
            simp [hacc] at had
          | inr halready => exact Or.inl halready
        | tail _ hmem => exact Or.inr ⟨d, hmem, had⟩

theorem ascend_ships_of_exists {β : Type} [DecidableEq β] (inc : Release β)
    (U : List (Release β)) (h : ∃ c, c ∈ U ∧ accepts inc c = true) :
    accepts inc (ascend inc U) = true :=
  ascend_ships (noRegress_refl inc) (Or.inl rfl) (Or.inr h)

theorem ascend_frontier {β : Type} [DecidableEq β] (inc : Release β) (U : List (Release β)) :
    (∀ c ∈ U, accepts (ascend inc U) c = false) ∧
      ascend inc U = ascendFuel U.length inc U :=
  ⟨ascend_maximal inc U, ascend_fuel inc U⟩

theorem shipped_step {β : Type} [DecidableEq β] (stream : Nat → Release β) (n : Nat) :
    noRegress (shipped stream n) (shipped stream (n + 1)) = true := by
  simp [shipped, step_noRegress]

theorem shipped_add {β : Type} [DecidableEq β] (stream : Nat → Release β) (m k : Nat) :
    noRegress (shipped stream m) (shipped stream (m + k)) = true := by
  induction k with
  | zero => simp [noRegress_refl]
  | succ k ih =>
    rw [Nat.add_succ]
    exact noRegress_trans ih (shipped_step stream (m + k))

theorem shipped_chain {β : Type} [DecidableEq β] (stream : Nat → Release β) {m n : Nat}
    (h : m ≤ n) : noRegress (shipped stream m) (shipped stream n) = true := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h
  simpa [hk] using shipped_add stream m k

theorem policy_exists {β : Type} [DecidableEq β] (stream : Nat → Release β) :
    ∃ ship : Nat → Release β,
      ship 0 = stream 0 ∧
        ∀ n, noRegress (ship n) (ship (n + 1)) = true ∧
          (ship (n + 1) = stream (n + 1) ∨ ship (n + 1) = ship n) := by
  refine ⟨shipped stream, rfl, ?_⟩
  intro n
  refine ⟨shipped_step stream n, ?_⟩
  simpa [shipped] using (step_witness (shipped stream n) (stream (n + 1))).2

end SoftwareDoesntRegress
