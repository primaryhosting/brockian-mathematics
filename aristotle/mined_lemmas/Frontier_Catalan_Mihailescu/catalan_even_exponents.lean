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
