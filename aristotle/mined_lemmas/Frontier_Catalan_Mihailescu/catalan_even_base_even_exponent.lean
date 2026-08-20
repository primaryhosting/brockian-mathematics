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
