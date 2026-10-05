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

theorem isPerfectPower_iff_prime_exponent (n : ℕ) :
    IsPerfectPower n ↔ ∃ a p : ℕ, 1 < a ∧ p.Prime ∧ n = a ^ p := by
  constructor
  · rintro ⟨a, k, ha, hk, rfl⟩
    refine ⟨a ^ (k / k.minFac), k.minFac, ?_, Nat.minFac_prime (by omega), ?_⟩
    · have h1 : 1 ≤ k / k.minFac :=
        Nat.one_le_div_iff (Nat.minFac_pos k) |>.mpr (Nat.minFac_le (by omega))
      calc 1 = a ^ 0 := (pow_zero a).symm
      _ < a ^ (k / k.minFac) := Nat.pow_lt_pow_right ha (by omega)
    · rw [← pow_mul, Nat.div_mul_cancel (Nat.minFac_dvd k)]
  · rintro ⟨a, p, ha, hp, rfl⟩
    exact ⟨a, p, ha, hp.one_lt, rfl⟩

/-- **Lean-checked reduction**: the Catalan–Mihailescu statement is equivalent to its
restriction to prime exponents. -/
