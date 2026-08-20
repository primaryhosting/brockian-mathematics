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
