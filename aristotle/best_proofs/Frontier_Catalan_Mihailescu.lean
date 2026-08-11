import Mathlib

/-!
# Catalan Mihailescu
Category: Frontier — Prime Numbers
Target: Frontier.Catalan_Mihailescu
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

Mihailescu's theorem (Catalan's conjecture) states that `8` and `9` are the only two
consecutive perfect powers, i.e. that the only solution of `x ^ p - y ^ q = 1` in natural
numbers `x, y, p, q ≥ 2` is `3 ^ 2 - 2 ^ 3 = 1`.

This file

* formalizes the statement (`Frontier.CatalanStatement`, together with its
  integer-subtraction form `Frontier.CatalanStatementInt` and its "only consecutive perfect
  powers" form `Frontier.ConsecutivePerfectPowersStatement`, both proved equivalent to it);
* proves a **reduction**: the general statement follows from the special case in which both
  exponents are prime (`Frontier.catalan_reduction_to_prime_exponents`);
* proves several **base cases** of the conjecture unconditionally, among them the complete
  case `y = 2` (`Frontier.catalan_base_two_right`, which contains the actual Catalan
  solution `3 ^ 2 = 2 ^ 3 + 1`) and the complete case `x = 2`
  (`Frontier.catalan_base_two_left`);
* verifies the statement exhaustively in a finite range
  (`Frontier.catalan_bounded`).

The target theorem `Frontier.Catalan_Mihailescu` collects these verified results.  The full
theorem of Mihailescu is *not* proved here.
-/

namespace Frontier

/-! ### Elementary helper lemmas -/

/-- If `x` is odd and `p` is odd, then `x - 1` splits off an *odd* cofactor of `x ^ p - 1`. -/
lemma geom_factor_odd (x : ℤ) (p : ℕ) (hx : Odd x) (hp : Odd p) :
    ∃ T : ℤ, T % 2 = 1 ∧ T * (x - 1) = x ^ p - 1 := by
  refine ⟨∑ i ∈ Finset.range p, x ^ i, ?_, geom_sum_mul x p⟩
  rw [Finset.sum_int_mod]
  have h1 : ∀ i ∈ Finset.range p, x ^ i % 2 = 1 := by
    intro i _
    rw [← Int.odd_iff]
    exact hx.pow
  rw [Finset.sum_congr rfl h1]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  rw [← Int.odd_iff]
  exact (Int.odd_coe_nat p).2 hp

/-- An odd divisor of a power of two is a unit. -/
lemma odd_dvd_two_pow (T : ℤ) (q : ℕ) (hT : T % 2 = 1) (h : T ∣ 2 ^ q) : T = 1 ∨ T = -1 := by
  have h1 : T.natAbs ∣ (2:ℤ).natAbs ^ q := by
    rw [← Int.natAbs_pow]
    exact Int.natAbs_dvd_natAbs.2 h
  have h2 : Nat.Coprime T.natAbs 2 :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by omega)).symm
  have := (h2.pow_right q).eq_one_of_dvd (by simpa using h1)
  omega

/-- `3` is not a power of two. -/
lemma two_pow_ne_three (b : ℕ) : (2:ℕ) ^ b ≠ 3 := by
  match b with
  | 0 => norm_num
  | (b + 1) =>
    have h : (2:ℕ) ∣ 2 ^ (b + 1) := ⟨2 ^ b, by ring⟩
    omega

/-- A power `x ^ k` with `x ≥ 2` equals `2` only for `x = 2` and `k = 1`. -/
lemma pow_eq_two {x k : ℕ} (hx : 2 ≤ x) (h : x ^ k = 2) : x = 2 ∧ k = 1 := by
  match k with
  | 0 => simp at h
  | 1 => simpa using h
  | (k + 2) =>
    exfalso
    have h1 : 2 ^ (k + 2) ≤ x ^ (k + 2) := Nat.pow_le_pow_left hx _
    have h2 : 2 ^ 2 ≤ 2 ^ (k + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    norm_num at h2
    omega

/-- A power `x ^ k` with `x ≥ 2` equals `3` only for `x = 3` and `k = 1`. -/
lemma pow_eq_three {x k : ℕ} (hx : 2 ≤ x) (h : x ^ k = 3) : x = 3 ∧ k = 1 := by
  match k with
  | 0 => simp at h
  | 1 => simpa using h
  | (k + 2) =>
    exfalso
    have h1 : 2 ^ (k + 2) ≤ x ^ (k + 2) := Nat.pow_le_pow_left hx _
    have h2 : 2 ^ 2 ≤ 2 ^ (k + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    norm_num at h2
    omega

/-- `(y + 1) ^ n` exceeds `y ^ n` by more than `1`, for `y ≥ 2` and `n ≥ 2`. -/
lemma succ_pow_add_two_le {y n : ℕ} (hy : 2 ≤ y) (hn : 2 ≤ n) : y ^ n + 2 ≤ (y + 1) ^ n := by
  induction n, hn using Nat.le_induction with
  | base => nlinarith [sq_nonneg y]
  | succ n hn ih =>
    have hyn : 1 ≤ y ^ n := Nat.one_le_pow _ _ (by omega)
    have h1 : (y ^ n + 2) * (y + 1) ≤ (y + 1) ^ n * (y + 1) := Nat.mul_le_mul_right _ ih
    have h2 : y ^ (n + 1) + 2 ≤ (y ^ n + 2) * (y + 1) := by
      have hpow : y ^ (n + 1) = y ^ n * y := by ring
      nlinarith
    calc y ^ (n + 1) + 2 ≤ (y ^ n + 2) * (y + 1) := h2
      _ ≤ (y + 1) ^ n * (y + 1) := h1
      _ = (y + 1) ^ (n + 1) := by ring

/-! ### The statement -/

/-- **Catalan's conjecture / Mihailescu's theorem.**  The only pair of consecutive perfect
powers is `8, 9`: if `x ^ p = y ^ q + 1` with `x, y, p, q ≥ 2`, then `x = 3`, `p = 2`,
`y = 2`, `q = 3`. -/
def CatalanStatement : Prop :=
  ∀ x y p q : ℕ, 2 ≤ x → 2 ≤ y → 2 ≤ p → 2 ≤ q → x ^ p = y ^ q + 1 →
    x = 3 ∧ p = 2 ∧ y = 2 ∧ q = 3

/-- The same statement, written with integer subtraction as `x ^ p - y ^ q = 1`. -/
def CatalanStatementInt : Prop :=
  ∀ x y p q : ℕ, 2 ≤ x → 2 ≤ y → 2 ≤ p → 2 ≤ q → (x : ℤ) ^ p - (y : ℤ) ^ q = 1 →
    x = 3 ∧ p = 2 ∧ y = 2 ∧ q = 3

/-- `n` is a perfect power, i.e. `n = a ^ k` with `a, k ≥ 2`. -/
def IsPerfectPower (n : ℕ) : Prop := ∃ a k : ℕ, 2 ≤ a ∧ 2 ≤ k ∧ n = a ^ k

/-- Catalan's conjecture phrased as "`8` and `9` are the only consecutive perfect powers". -/
def ConsecutivePerfectPowersStatement : Prop :=
  ∀ n : ℕ, IsPerfectPower n → IsPerfectPower (n + 1) → n = 8

/-- The special case of Catalan's conjecture in which both exponents are prime. -/
def CatalanStatementPrimeExponents : Prop :=
  ∀ x y p q : ℕ, 2 ≤ x → 2 ≤ y → p.Prime → q.Prime → x ^ p = y ^ q + 1 →
    x = 3 ∧ p = 2 ∧ y = 2 ∧ q = 3

/-- The natural-number and the integer-subtraction forms of the statement are equivalent. -/
theorem catalanStatement_iff_int : CatalanStatement ↔ CatalanStatementInt := by
  constructor
  · intro H x y p q hx hy hp hq h
    refine H x y p q hx hy hp hq ?_
    have hc : ((x ^ p : ℕ) : ℤ) = ((y ^ q + 1 : ℕ) : ℤ) := by push_cast; linarith
    exact_mod_cast hc
  · intro H x y p q hx hy hp hq h
    refine H x y p q hx hy hp hq ?_
    have hc : ((x ^ p : ℕ) : ℤ) = ((y ^ q + 1 : ℕ) : ℤ) :=
      by exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) h
    push_cast at hc
    linarith

/-- A power `y ^ q` with `y, q ≥ 2` equals `8` only for `y = 2`, `q = 3`. -/
lemma pow_eq_eight {y q : ℕ} (hy : 2 ≤ y) (hq : 2 ≤ q) (h : y ^ q = 8) : y = 2 ∧ q = 3 := by
  have hy2 : y = 2 := by
    by_contra hc
    have h3 : 3 ≤ y := by omega
    have : 3 ^ 2 ≤ y ^ q :=
      le_trans (Nat.pow_le_pow_left h3 2) (Nat.pow_le_pow_right (by omega) hq)
    omega
  subst hy2
  exact ⟨rfl, Nat.pow_right_injective (le_refl 2) (by omega : (2:ℕ) ^ q = 2 ^ 3)⟩

/-- A power `x ^ p` with `x, p ≥ 2` equals `9` only for `x = 3`, `p = 2`. -/
lemma pow_eq_nine {x p : ℕ} (hx : 2 ≤ x) (hp : 2 ≤ p) (h : x ^ p = 9) : x = 3 ∧ p = 2 := by
  have hx4 : x < 4 := by
    by_contra hc
    have h4 : 4 ≤ x := by omega
    have : 4 ^ 2 ≤ x ^ p :=
      le_trans (Nat.pow_le_pow_left h4 2) (Nat.pow_le_pow_right (by omega) hp)
    omega
  interval_cases x
  · exfalso
    have h1 : Even ((2:ℕ) ^ p) := (Nat.even_pow).mpr ⟨even_two, by omega⟩
    rw [h] at h1
    rcases h1 with ⟨c, hc⟩
    omega
  · exact ⟨rfl, Nat.pow_right_injective (by norm_num) (by omega : (3:ℕ) ^ p = 3 ^ 2)⟩

/-- The equation form and the "consecutive perfect powers" form of the statement agree. -/
theorem catalanStatement_iff_consecutive :
    CatalanStatement ↔ ConsecutivePerfectPowersStatement := by
  constructor
  · intro H n ⟨y, q, hy, hq, hn⟩ ⟨x, p, hx, hp, hn1⟩
    obtain ⟨-, -, hy2, hq3⟩ := H x y p q hx hy hp hq (by omega)
    subst hy2; subst hq3
    omega
  · intro H x y p q hx hy hp hq h
    have hn : y ^ q = 8 := H (y ^ q) ⟨y, q, hy, hq, rfl⟩ ⟨x, p, hx, hp, by omega⟩
    obtain ⟨hy2, hq3⟩ := pow_eq_eight hy hq hn
    obtain ⟨hx3, hp2⟩ := pow_eq_nine hx hp (by omega)
    exact ⟨hx3, hp2, hy2, hq3⟩

/-! ### A Lean-checked reduction to prime exponents -/

/-- **Reduction.**  It suffices to prove Catalan's conjecture for prime exponents:
replacing `p` by its smallest prime factor `r` (and `x` by `x ^ (p / r)`), and likewise for
`q`, turns an arbitrary solution into one with prime exponents. -/
theorem catalan_reduction_to_prime_exponents :
    CatalanStatementPrimeExponents → CatalanStatement := by
  intro H x y p q hx hy hp hq h
  have hrp : (p.minFac).Prime := Nat.minFac_prime (by omega)
  obtain ⟨k, hk⟩ : p.minFac ∣ p := Nat.minFac_dvd p
  have hsp : (q.minFac).Prime := Nat.minFac_prime (by omega)
  obtain ⟨l, hl⟩ : q.minFac ∣ q := Nat.minFac_dvd q
  have hk0 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [h0, mul_zero] at hk; omega
    · exact h0
  have hl0 : 1 ≤ l := by
    rcases Nat.eq_zero_or_pos l with h0 | h0
    · rw [h0, mul_zero] at hl; omega
    · exact h0
  have hX : 2 ≤ x ^ k := le_trans hx (Nat.le_self_pow (by omega) x)
  have hY : 2 ≤ y ^ l := le_trans hy (Nat.le_self_pow (by omega) y)
  have key : (x ^ k) ^ p.minFac = (y ^ l) ^ q.minFac + 1 := by
    rw [← pow_mul, ← pow_mul, mul_comm k p.minFac, mul_comm l q.minFac, ← hk, ← hl]
    exact h
  obtain ⟨h1, h2, h3, h4⟩ := H (x ^ k) (y ^ l) p.minFac q.minFac hX hY hrp hsp key
  obtain ⟨hx3, hk1⟩ := pow_eq_three hx h1
  obtain ⟨hy2, hl1⟩ := pow_eq_two hy h3
  exact ⟨hx3, by rw [hk, h2, hk1, mul_one], hy2, by rw [hl, h4, hl1, mul_one]⟩

/-! ### Base cases -/

/-- **Base case `y = 2`.**  The only perfect power that is one more than a power of two is
`9 = 2 ^ 3 + 1`.  (This case contains the actual Catalan solution.)

For even `p` one factors `z ^ 2 - 1 = (z - 1)(z + 1) = 2 ^ q`; for odd `p` the cofactor of
`x - 1` in `x ^ p - 1` is odd, hence a unit, which forces `x ^ p = x`. -/
theorem catalan_base_two_right (x p q : ℕ) (hx : 2 ≤ x) (hp : 2 ≤ p) (hq : 2 ≤ q)
    (h : x ^ p = 2 ^ q + 1) : x = 3 ∧ p = 2 ∧ q = 3 := by
  rcases Nat.even_or_odd p with hpe | hpo
  · obtain ⟨k, hk⟩ := hpe
    have hk1 : 1 ≤ k := by omega
    set z := x ^ k with hz
    have hz2 : 2 ≤ z := le_trans hx (Nat.le_self_pow (by omega) x)
    have hsq : z ^ 2 = 2 ^ q + 1 := by
      rw [hz, ← pow_mul, show k * 2 = k + k by ring, ← hk]
      exact h
    obtain ⟨m, hm⟩ : ∃ m, z = m + 1 := ⟨z - 1, by omega⟩
    have hmm : m * (m + 2) = 2 ^ q := by
      have h' : (m + 1) ^ 2 = 2 ^ q + 1 := by rw [← hm]; exact hsq
      nlinarith
    have hdvd1 : m ∣ 2 ^ q := ⟨m + 2, hmm.symm⟩
    have hdvd2 : (m + 2) ∣ 2 ^ q := ⟨m, by rw [← hmm]; ring⟩
    obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd1
    obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd2
    have hm2 : m = 2 := by
      match a with
      | 0 =>
        exfalso
        norm_num at ha
        rw [ha] at hb
        exact two_pow_ne_three b (by omega)
      | 1 => norm_num at ha; omega
      | (a + 2) =>
        exfalso
        have h4a : (4 : ℕ) ∣ 2 ^ (a + 2) := ⟨2 ^ a, by ring⟩
        have hb2 : 2 ^ 2 < 2 ^ b := by
          have h2 : 2 ^ 2 ≤ 2 ^ (a + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
        have hb' : 2 < b := (Nat.pow_lt_pow_iff_right (by norm_num)).1 hb2
        have h4b : (4 : ℕ) ∣ 2 ^ b := by
          have h2 : (2:ℕ) ^ 2 ∣ 2 ^ b := Nat.pow_dvd_pow 2 (by omega)
          simpa using h2
        omega
    have hz3 : z = 3 := by omega
    obtain ⟨hx3, hk1'⟩ := pow_eq_three hx (by rw [← hz]; exact hz3)
    refine ⟨hx3, by omega, ?_⟩
    rw [hz3] at hsq
    norm_num at hsq
    have h8 : (2:ℕ) ^ q = 2 ^ 3 := by norm_num; omega
    exact Nat.pow_right_injective (le_refl 2) h8
  · exfalso
    have hxodd : Odd x := by
      rcases Nat.even_or_odd x with hxe | hxo
      · exfalso
        have h1 : Even (x ^ p) := (Nat.even_pow).mpr ⟨hxe, by omega⟩
        have h2 : Even ((2:ℕ) ^ q) := (Nat.even_pow).mpr ⟨even_two, by omega⟩
        rw [h] at h1
        rcases h1 with ⟨c, hc⟩
        rcases h2 with ⟨d, hd⟩
        omega
      · exact hxo
    have hxZ : Odd (x : ℤ) := (Int.odd_coe_nat x).2 hxodd
    obtain ⟨T, hT, hTeq⟩ := geom_factor_odd (x : ℤ) p hxZ hpo
    have hcast : ((x:ℤ)) ^ p = (2:ℤ) ^ q + 1 := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) h
    have hpow : (x : ℤ) ^ p - 1 = 2 ^ q := by linarith
    rw [hpow] at hTeq
    have hdvd : T ∣ (2:ℤ) ^ q := ⟨(x : ℤ) - 1, hTeq.symm⟩
    have hx1 : (2 : ℤ) ≤ (x : ℤ) := by exact_mod_cast hx
    have hpos : (0 : ℤ) < 2 ^ q := by positivity
    rcases odd_dvd_two_pow T q hT hdvd with h1 | h1
    · rw [h1, one_mul] at hTeq
      have hlt : x < x ^ p := by
        calc x = x ^ 1 := (pow_one x).symm
          _ < x ^ p := Nat.pow_lt_pow_right (by omega) (by omega)
      have hxx : (x : ℤ) ^ p = (x : ℤ) := by linarith
      have hxn : (x ^ p : ℕ) = x := by exact_mod_cast hxx
      omega
    · rw [h1] at hTeq
      linarith

/-- **Base case `y = 2`, in the language of consecutive perfect powers.**  If `n` is a power
of two with exponent at least `2` and `n + 1` is a perfect power, then `n = 8`. -/
theorem consecutive_perfect_powers_of_two_pow (n q : ℕ) (hq : 2 ≤ q) (hn : n = 2 ^ q)
    (h : IsPerfectPower (n + 1)) : n = 8 := by
  obtain ⟨x, p, hx, hp, hxp⟩ := h
  obtain ⟨-, -, hq3⟩ := catalan_base_two_right x p q hx hp hq (by omega)
  subst hq3
  norm_num at hn
  exact hn

/-- **Base case `x = 2`.**  No power of two is one more than a perfect power.

For even `q` this is a congruence obstruction modulo `4`; for odd `q` the cofactor of
`y + 1` in `y ^ q + 1` is odd, hence a unit, which forces `y ^ q = y`. -/
theorem catalan_base_two_left (y p q : ℕ) (hy : 2 ≤ y) (hp : 2 ≤ p) (hq : 2 ≤ q) :
    2 ^ p ≠ y ^ q + 1 := by
  intro h
  have hyodd : Odd y := by
    rcases Nat.even_or_odd y with hye | hyo
    · exfalso
      have h1 : Even (y ^ q) := (Nat.even_pow).mpr ⟨hye, by omega⟩
      have h2 : Even ((2:ℕ) ^ p) := (Nat.even_pow).mpr ⟨even_two, by omega⟩
      rcases h1 with ⟨c, hc⟩
      rcases h2 with ⟨d, hd⟩
      omega
    · exact hyo
  rcases Nat.even_or_odd q with hqe | hqo
  · obtain ⟨k, hk⟩ := hqe
    have hk1 : 1 ≤ k := by omega
    set z := y ^ k with hz
    have hzodd : Odd z := hyodd.pow
    have hsq : z ^ 2 + 1 = 2 ^ p := by
      rw [hz, ← pow_mul, show k * 2 = k + k by ring, ← hk]
      omega
    have h4 : (4 : ℕ) ∣ 2 ^ p := by
      have h2 : (2:ℕ) ^ 2 ∣ 2 ^ p := Nat.pow_dvd_pow 2 (by omega)
      simpa using h2
    obtain ⟨m, hm⟩ := hzodd
    obtain ⟨c, hc⟩ := h4
    rw [hm] at hsq
    have e : (2 * m + 1) ^ 2 + 1 = 4 * (m * m + m) + 2 := by ring
    omega
  · have hyZ : Odd (-(y : ℤ)) := ((Int.odd_coe_nat y).2 hyodd).neg
    obtain ⟨T, hT, hTeq⟩ := geom_factor_odd (-(y : ℤ)) q hyZ hqo
    have hqpow : (-(y : ℤ)) ^ q = -((y : ℤ) ^ q) := hqo.neg_pow _
    have hcast : ((2:ℤ)) ^ p = (y:ℤ) ^ q + 1 := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) h
    have hTeq' : T * ((y : ℤ) + 1) = 2 ^ p := by
      rw [hqpow] at hTeq
      nlinarith [hTeq, hcast]
    have hdvd : T ∣ (2:ℤ) ^ p := ⟨(y : ℤ) + 1, hTeq'.symm⟩
    have hy1 : (2 : ℤ) ≤ (y : ℤ) := by exact_mod_cast hy
    have hpos : (0 : ℤ) < 2 ^ p := by positivity
    rcases odd_dvd_two_pow T p hT hdvd with h1 | h1
    · rw [h1, one_mul] at hTeq'
      have hlt : y < y ^ q := by
        calc y = y ^ 1 := (pow_one y).symm
          _ < y ^ q := Nat.pow_lt_pow_right (by omega) (by omega)
      have hyy : (y : ℤ) ^ q = (y : ℤ) := by linarith
      have hyn : (y ^ q : ℕ) = y := by exact_mod_cast hyy
      omega
    · rw [h1] at hTeq'
      linarith

/-- **Base case: equal exponents.**  `x ^ n = y ^ n + 1` has no solutions with `y, n ≥ 2`. -/
theorem catalan_equal_exponents (x y n : ℕ) (hy : 2 ≤ y) (hn : 2 ≤ n) : x ^ n ≠ y ^ n + 1 := by
  intro h
  have hyx : y < x := by
    by_contra hc
    push_neg at hc
    exact absurd (Nat.pow_le_pow_left hc n) (by omega)
  have h1 : (y + 1) ^ n ≤ x ^ n := Nat.pow_le_pow_left (by omega) n
  have h2 : y ^ n + 2 ≤ (y + 1) ^ n := succ_pow_add_two_le hy hn
  omega

/-- **Base case: both exponents even.**  No solutions. -/
theorem catalan_even_exponents (x y p q : ℕ) (hx : 2 ≤ x) (hy : 2 ≤ y) (hp : 2 ≤ p)
    (hq : 2 ≤ q) (hpe : Even p) (hqe : Even q) : x ^ p ≠ y ^ q + 1 := by
  intro h
  obtain ⟨a, ha⟩ := hpe
  obtain ⟨b, hb⟩ := hqe
  have hX : 2 ≤ x ^ a := le_trans hx (Nat.le_self_pow (by omega) x)
  have hY : 2 ≤ y ^ b := le_trans hy (Nat.le_self_pow (by omega) y)
  refine catalan_equal_exponents (x ^ a) (y ^ b) 2 hY (le_refl 2) ?_
  rw [← pow_mul, ← pow_mul, show a * 2 = a + a by ring, show b * 2 = b + b by ring, ← ha, ← hb]
  exact h

/-- **Base case: even base `x` with even exponent `q`.**  No solutions (a mod-`4`
obstruction). -/
theorem catalan_even_base_even_exponent (x y p q : ℕ) (hp : 2 ≤ p) (hxe : Even x)
    (hqe : Even q) : x ^ p ≠ y ^ q + 1 := by
  intro h
  obtain ⟨b, hb⟩ := hqe
  set z := y ^ b with hz
  have hsq : z ^ 2 + 1 = x ^ p := by
    rw [hz, ← pow_mul, show b * 2 = b + b by ring, ← hb]
    omega
  obtain ⟨a, ha⟩ := hxe
  have h4 : (4 : ℕ) ∣ x ^ p := by
    have h1 : x ^ 2 ∣ x ^ p := Nat.pow_dvd_pow x (by omega)
    have h2 : (4 : ℕ) ∣ x ^ 2 := ⟨a * a, by rw [ha]; ring⟩
    exact h2.trans h1
  obtain ⟨c, hc⟩ := h4
  rcases Nat.even_or_odd z with hze | hzo
  · obtain ⟨m, hm⟩ := hze
    rw [hm] at hsq
    have e : (m + m) ^ 2 + 1 = 4 * (m * m) + 1 := by ring
    omega
  · obtain ⟨m, hm⟩ := hzo
    rw [hm] at hsq
    have e : (2 * m + 1) ^ 2 + 1 = 4 * (m * m + m) + 2 := by ring
    omega

/-- **Exhaustive verification in a finite range**: for bases at most `30` and exponents at
most `6`, the only pair of consecutive perfect powers is `8, 9`. -/
theorem catalan_bounded : ∀ x ∈ Finset.range 31, ∀ y ∈ Finset.range 31, ∀ p ∈ Finset.range 7,
    ∀ q ∈ Finset.range 7, 2 ≤ x → 2 ≤ y → 2 ≤ p → 2 ≤ q → x ^ p = y ^ q + 1 →
    x = 3 ∧ p = 2 ∧ y = 2 ∧ q = 3 := by decide

/-! ### The target theorem -/

/--
**Catalan / Mihailescu.**  The proposition `Frontier.CatalanStatement` formalizes the claim
that `8` and `9` are the only consecutive perfect powers.  Mihailescu's full theorem is not
proved here; what *is* proved, and collected in this theorem, is:

1. `3 ^ 2 = 2 ^ 3 + 1`, i.e. `8` and `9` really are consecutive perfect powers;
2. the natural-number and integer-subtraction forms of the statement are equivalent;
3. the equation form and the "consecutive perfect powers" form are equivalent;
4. a **reduction**: the full statement follows from the case of prime exponents;
5. the **base case `y = 2`**: `x ^ p = 2 ^ q + 1` forces `(x, p, q) = (3, 2, 3)`;
6. the same base case in the language of perfect powers: a power of two `n` (with exponent
   at least `2`) such that `n + 1` is a perfect power must be `8`;
7. the **base case `x = 2`**: `2 ^ p = y ^ q + 1` has no solutions;
8. the case of **equal exponents**;
9. the case of **two even exponents**;
10. the case of an **even base `x` together with an even exponent `q`**;
11. an **exhaustive check** for bases at most `30` and exponents at most `6`.
-/
theorem Catalan_Mihailescu :
    (3 ^ 2 = 2 ^ 3 + 1) ∧
    (CatalanStatement ↔ CatalanStatementInt) ∧
    (CatalanStatement ↔ ConsecutivePerfectPowersStatement) ∧
    (CatalanStatementPrimeExponents → CatalanStatement) ∧
    (∀ x p q : ℕ, 2 ≤ x → 2 ≤ p → 2 ≤ q → x ^ p = 2 ^ q + 1 → x = 3 ∧ p = 2 ∧ q = 3) ∧
    (∀ n q : ℕ, 2 ≤ q → n = 2 ^ q → IsPerfectPower (n + 1) → n = 8) ∧
    (∀ y p q : ℕ, 2 ≤ y → 2 ≤ p → 2 ≤ q → 2 ^ p ≠ y ^ q + 1) ∧
    (∀ x y n : ℕ, 2 ≤ y → 2 ≤ n → x ^ n ≠ y ^ n + 1) ∧
    (∀ x y p q : ℕ, 2 ≤ x → 2 ≤ y → 2 ≤ p → 2 ≤ q → Even p → Even q → x ^ p ≠ y ^ q + 1) ∧
    (∀ x y p q : ℕ, 2 ≤ p → Even x → Even q → x ^ p ≠ y ^ q + 1) ∧
    (∀ x ∈ Finset.range 31, ∀ y ∈ Finset.range 31, ∀ p ∈ Finset.range 7,
      ∀ q ∈ Finset.range 7, 2 ≤ x → 2 ≤ y → 2 ≤ p → 2 ≤ q → x ^ p = y ^ q + 1 →
      x = 3 ∧ p = 2 ∧ y = 2 ∧ q = 3) :=
  ⟨by norm_num, catalanStatement_iff_int, catalanStatement_iff_consecutive,
    catalan_reduction_to_prime_exponents, catalan_base_two_right,
    consecutive_perfect_powers_of_two_pow, catalan_base_two_left, catalan_equal_exponents,
    catalan_even_exponents, catalan_even_base_even_exponent, catalan_bounded⟩

end Frontier

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

