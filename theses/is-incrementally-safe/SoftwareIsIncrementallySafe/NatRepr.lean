private def digitVal (c : Char) : Nat :=
  c.toNat - '0'.toNat

private theorem digitVal_digitChar {n : Nat} (h : n < 10) :
    digitVal (Nat.digitChar n) = n := by
  match n with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | 3 => decide
  | 4 => decide
  | 5 => decide
  | 6 => decide
  | 7 => decide
  | 8 => decide
  | 9 => decide
  | n + 10 => exact absurd h (Nat.not_lt_of_le (Nat.le_add_left 10 n))

private def ofDigits : List Char → Nat
  | [] => 0
  | c :: cs => digitVal c * 10 ^ cs.length + ofDigits cs

private theorem div10_bound (fuel n : Nat) (h : n < 10 ^ (fuel + 1)) :
    n / 10 < 10 ^ fuel := by
  match Nat.lt_or_ge (n / 10) (10 ^ fuel) with
  | Or.inl hlt => exact hlt
  | Or.inr hge =>
    have hsum : (n / 10) * 10 + n % 10 = n := by
      rw [Nat.mul_comm]
      exact Nat.div_add_mod n 10
    have hq : (n / 10) * 10 ≤ n :=
      Nat.le_trans (Nat.le_add_right ((n / 10) * 10) (n % 10)) (Nat.le_of_eq hsum)
    have hmul : 10 ^ fuel * 10 ≤ (n / 10) * 10 := Nat.mul_le_mul_right 10 hge
    have hpow : 10 ^ (fuel + 1) ≤ n := by
      rw [Nat.pow_succ]
      exact Nat.le_trans hmul hq
    exact absurd h (Nat.not_lt_of_le hpow)

private theorem lt_ten_pow (n : Nat) : n < 10 ^ (n + 1) := by
  induction n with
  | zero => decide
  | succ n ih =>
    have hp : 0 < 10 ^ (n + 1) := Nat.pow_pos (by decide)
    have hle : n + 1 ≤ 10 ^ (n + 1) := Nat.succ_le_of_lt ih
    have hmul : 10 ^ (n + 1) * 1 < 10 ^ (n + 1) * 10 :=
      Nat.mul_lt_mul_of_pos_left (by decide : 1 < 10) hp
    rw [Nat.mul_one] at hmul
    have hmul' : 10 ^ (n + 1) < 10 ^ (n + 2) := by
      rw [Nat.pow_succ]
      exact hmul
    exact Nat.lt_of_le_of_lt hle hmul'

private theorem core_step (q r o p : Nat) :
    q * (p * 10) + (r * p + o) = (10 * q + r) * p + o := by
  rw [Nat.add_mul, Nat.add_assoc, Nat.mul_assoc, Nat.mul_left_comm q p 10, Nat.mul_comm q 10]
  ac_rfl

private theorem core_ofDigits (fuel n : Nat) (ds : List Char)
    (h : n < 10 ^ fuel) :
    ofDigits (Nat.toDigitsCore 10 fuel n ds) =
      n * 10 ^ ds.length + ofDigits ds := by
  induction fuel generalizing n ds with
  | zero =>
    have hn : n = 0 := Nat.lt_one_iff.mp h
    subst hn
    rw [Nat.toDigitsCore, Nat.zero_mul, Nat.zero_add]
  | succ fuel ih =>
    rw [Nat.toDigitsCore]
    split
    · rename_i hz
      have hsum : 10 * (n / 10) + n % 10 = n := Nat.div_add_mod n 10
      have hmod : n % 10 = n := by
        rw [hz, Nat.mul_zero, Nat.zero_add] at hsum
        exact hsum
      have hnlt : n < 10 := hmod ▸ Nat.mod_lt n (by decide)
      rw [ofDigits, hmod, digitVal_digitChar hnlt]
    · have hdiv : n / 10 < 10 ^ fuel := div10_bound fuel n h
      rw [ih (n / 10) (Nat.digitChar (n % 10) :: ds) hdiv]
      have hdig : digitVal (Nat.digitChar (n % 10)) = n % 10 :=
        digitVal_digitChar (Nat.mod_lt n (by decide))
      have hsplit : 10 * (n / 10) + n % 10 = n := Nat.div_add_mod n 10
      rw [List.length_cons, ofDigits, hdig, Nat.pow_succ]
      have hstep := core_step (n / 10) (n % 10) (ofDigits ds) (10 ^ ds.length)
      rw [hsplit] at hstep
      exact hstep

theorem Nat.repr_injective {a b : Nat} (h : Nat.repr a = Nat.repr b) : a = b := by
  have hdigits : Nat.toDigits 10 a = Nat.toDigits 10 b := by
    have hdata := congrArg String.data h
    simpa [Nat.repr, List.asString] using hdata
  have ha : ofDigits (Nat.toDigits 10 a) = a := by
    have hcore := core_ofDigits (a + 1) a [] (lt_ten_pow a)
    simpa [Nat.toDigits, Nat.mul_one, ofDigits] using hcore
  have hb : ofDigits (Nat.toDigits 10 b) = b := by
    have hcore := core_ofDigits (b + 1) b [] (lt_ten_pow b)
    simpa [Nat.toDigits, Nat.mul_one, ofDigits] using hcore
  rw [← ha, ← hb, hdigits]

