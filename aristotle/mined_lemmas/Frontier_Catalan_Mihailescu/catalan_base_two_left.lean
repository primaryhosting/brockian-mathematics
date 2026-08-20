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
