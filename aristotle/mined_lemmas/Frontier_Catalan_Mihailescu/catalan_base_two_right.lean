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
