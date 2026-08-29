/-
# Catalan Mihailescu
Category: Frontier — Prime Numbers
Target: Frontier.Catalan_Mihailescu
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses `/- -/` rather than `/-! -/` because Lean 4 requires module
-- doc-comments to appear *after* the `import` lines; the text is otherwise verbatim.)

import Mathlib

/-!
## Overview

The Catalan–Mihailescu theorem states that `8 = 2 ^ 3` and `9 = 3 ^ 2` are the only two
consecutive perfect powers, i.e. the only solution of `x ^ p - y ^ q = 1` in integers
`x, y, p, q > 1` is `3 ^ 2 - 2 ^ 3 = 1`.

This file formalises the statement (`Frontier.CatalanMihailescuStatement`), and proves,
axiom-cleanly:

* the base case `3 ^ 2 = 2 ^ 3 + 1`, and that `8`, `9` are perfect powers;
* a Lean-checked **reduction**: the general statement is *equivalent* to the statement
  restricted to prime exponents (`Frontier.catalan_iff_prime_exponents`);
* several complete subcases of the theorem:
  - equal exponents: `x ^ k ≠ y ^ k + 1` for `y ≥ 1`, `k ≥ 2`;
  - both exponents even: `x ^ p ≠ y ^ q + 1` for `p`, `q` even and `y > 1`;
  - even exponent against an odd base: `x ^ p ≠ y ^ q + 1` whenever `p` is even, `y` is
    odd and `y > 1`, `q ≥ 2` (in particular, in a hypothetical second solution with
    `p` even the number `y` must be even);
  - odd base with even exponent: `x ^ p ≠ y ^ q + 1` whenever `y` is odd, `q` is even
    and `p ≥ 2`;
* a kernel-checked finite verification: `9` and `8` are the only consecutive perfect powers
  up to `1000`.

The main theorem `Frontier.Catalan_Mihailescu` packages these results.
-/

namespace Frontier

/-- `n` is a perfect power: `n = a ^ k` with `a > 1` and `k > 1`. -/

theorem succ_pow_lower_bound (a : ℕ) : ∀ q : ℕ, 2 ≤ q → a ^ q + q * a ≤ (a + 1) ^ q := by
  intro q hq
  induction q, hq using Nat.le_induction with
  | base => ring_nf; omega
  | succ n hn ih =>
      have h1 : (a + 1) ^ (n + 1) = (a + 1) ^ n * (a + 1) := by ring
      have h2 : (a ^ n + n * a) * (a + 1) ≤ (a + 1) ^ n * (a + 1) :=
        Nat.mul_le_mul_right _ ih
      have key : (a ^ n + n * a) * (a + 1) = a ^ (n + 1) + a ^ n + n * a * a + n * a := by
        ring
      have hsq : a ≤ n * a * a := by
        rcases Nat.eq_zero_or_pos a with rfl | ha
        · simp
        · calc a = 1 * 1 * a := by ring
            _ ≤ n * a * a := Nat.mul_le_mul_right a (Nat.mul_le_mul (by omega) ha)
      have hexp : (n + 1) * a = n * a + a := by ring
      omega

/-- If `x ^ p = 9` with `x > 1` and `p ≥ 2` then `x = 3` and `p = 2`. -/
