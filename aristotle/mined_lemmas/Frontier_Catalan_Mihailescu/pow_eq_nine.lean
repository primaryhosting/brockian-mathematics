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

lemma pow_eq_nine {x p : ℕ} (hx : 2 ≤ x) (hp : 2 ≤ p) (h : x ^ p = 9) : x = 3 ∧ p = 2 := by
  have hx4 : x < 4 := by
    by_contra hc
    have h4 : 4 ≤ x := by omega
    have : 4 ^ 2 ≤ x ^ p :=
      le_trans (Nat.pow_le_pow_left h4 2) (Nat.pow_le_pow_right (by omega) hp)
    omega
  interval_cases x
  · exfalso
    have h1 : Even ((2:ℕ) ^ p) := (Nat.even_pow).mpr ⟨even_two, by omega⟩
    rw [h] at h1
    rcases h1 with ⟨c, hc⟩
    omega
  · exact ⟨rfl, Nat.pow_right_injective (by norm_num) (by omega : (3:ℕ) ^ p = 3 ^ 2)⟩

/-- The equation form and the "consecutive perfect powers" form of the statement agree. -/
