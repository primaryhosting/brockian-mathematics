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

lemma succ_pow_add_two_le {y n : ℕ} (hy : 2 ≤ y) (hn : 2 ≤ n) : y ^ n + 2 ≤ (y + 1) ^ n := by
  induction n, hn using Nat.le_induction with
  | base => nlinarith [sq_nonneg y]
  | succ n hn ih =>
    have hyn : 1 ≤ y ^ n := Nat.one_le_pow _ _ (by omega)
    have h1 : (y ^ n + 2) * (y + 1) ≤ (y + 1) ^ n * (y + 1) := Nat.mul_le_mul_right _ ih
    have h2 : y ^ (n + 1) + 2 ≤ (y ^ n + 2) * (y + 1) := by
      have hpow : y ^ (n + 1) = y ^ n * y := by ring
      nlinarith
    calc y ^ (n + 1) + 2 ≤ (y ^ n + 2) * (y + 1) := h2
      _ ≤ (y + 1) ^ n * (y + 1) := h1
      _ = (y + 1) ^ (n + 1) := by ring

/-! ### The statement -/

/-- **Catalan's conjecture / Mihailescu's theorem.**  The only pair of consecutive perfect
powers is `8, 9`: if `x ^ p = y ^ q + 1` with `x, y, p, q ≥ 2`, then `x = 3`, `p = 2`,
`y = 2`, `q = 3`. -/
