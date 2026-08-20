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

theorem catalanStatement_iff_consecutive :
    CatalanStatement ↔ ConsecutivePerfectPowersStatement := by
  constructor
  · intro H n ⟨y, q, hy, hq, hn⟩ ⟨x, p, hx, hp, hn1⟩
    obtain ⟨-, -, hy2, hq3⟩ := H x y p q hx hy hp hq (by omega)
    subst hy2; subst hq3
    omega
  · intro H x y p q hx hy hp hq h
    have hn : y ^ q = 8 := H (y ^ q) ⟨y, q, hy, hq, rfl⟩ ⟨x, p, hx, hp, by omega⟩
    obtain ⟨hy2, hq3⟩ := pow_eq_eight hy hq hn
    obtain ⟨hx3, hp2⟩ := pow_eq_nine hx hp (by omega)
    exact ⟨hx3, hp2, hy2, hq3⟩

/-! ### A Lean-checked reduction to prime exponents -/

/-- **Reduction.**  It suffices to prove Catalan's conjecture for prime exponents:
replacing `p` by its smallest prime factor `r` (and `x` by `x ^ (p / r)`), and likewise for
`q`, turns an arbitrary solution into one with prime exponents. -/
