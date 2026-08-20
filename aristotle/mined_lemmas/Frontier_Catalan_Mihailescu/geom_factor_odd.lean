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

lemma geom_factor_odd (x : ℤ) (p : ℕ) (hx : Odd x) (hp : Odd p) :
    ∃ T : ℤ, T % 2 = 1 ∧ T * (x - 1) = x ^ p - 1 := by
  refine ⟨∑ i ∈ Finset.range p, x ^ i, ?_, geom_sum_mul x p⟩
  rw [Finset.sum_int_mod]
  have h1 : ∀ i ∈ Finset.range p, x ^ i % 2 = 1 := by
    intro i _
    rw [← Int.odd_iff]
    exact hx.pow
  rw [Finset.sum_congr rfl h1]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  rw [← Int.odd_iff]
  exact (Int.odd_coe_nat p).2 hp

/-- An odd divisor of a power of two is a unit. -/
