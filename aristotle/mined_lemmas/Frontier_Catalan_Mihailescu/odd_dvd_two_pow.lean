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

lemma odd_dvd_two_pow (T : ℤ) (q : ℕ) (hT : T % 2 = 1) (h : T ∣ 2 ^ q) : T = 1 ∨ T = -1 := by
  have h1 : T.natAbs ∣ (2:ℤ).natAbs ^ q := by
    rw [← Int.natAbs_pow]
    exact Int.natAbs_dvd_natAbs.2 h
  have h2 : Nat.Coprime T.natAbs 2 :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by omega)).symm
  have := (h2.pow_right q).eq_one_of_dvd (by simpa using h1)
  omega

/-- `3` is not a power of two. -/
