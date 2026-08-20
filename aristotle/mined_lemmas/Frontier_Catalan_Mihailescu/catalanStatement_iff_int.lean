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
