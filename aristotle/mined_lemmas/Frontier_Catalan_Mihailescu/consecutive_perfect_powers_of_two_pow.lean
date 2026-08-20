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
