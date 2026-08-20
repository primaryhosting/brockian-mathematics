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
