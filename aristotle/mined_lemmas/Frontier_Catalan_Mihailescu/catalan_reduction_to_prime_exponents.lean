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
