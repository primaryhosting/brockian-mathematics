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

theorem mem_perfectPowersUpTo1000 {n : ℕ} (hn : IsPerfectPower n) (h : n ≤ 1000) :
    n ∈ perfectPowersUpTo1000 := by
  obtain ⟨a, k, ha, hk, rfl⟩ := hn
  have h2 : a ^ 2 ≤ a ^ k := Nat.pow_le_pow_right (by omega) hk
  have hasq : a * a ≤ 1000 := by nlinarith [pow_two a]
  have ha31 : a ≤ 31 := by nlinarith
  have h2k : 2 ^ k ≤ a ^ k := Nat.pow_le_pow_left ha k
  have hk9 : k ≤ 9 := by
    by_contra hc
    push_neg at hc
    have : 2 ^ 10 ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  clear h2 hasq h2k
  interval_cases a <;> interval_cases k <;> revert h <;> decide

/-- The Catalan–Mihailescu statement, verified for all perfect powers up to `1000`. -/
