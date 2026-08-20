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

Catalan's conjecture, proved by Mihailescu (2004), states that the only pair of consecutive
perfect powers is `8 = 2 ^ 3` and `9 = 3 ^ 2`; equivalently the only solution of
`x ^ p - y ^ q = 1` in integers `x, y, p, q > 1` is `3 ^ 2 - 2 ^ 3 = 1`.

Mihailescu's theorem is **not** available in Mathlib (a search of Mathlib turns up no
`Catalan`/`Mihailescu` result about the exponential Diophantine equation; the files mentioning
"Catalan" concern Catalan *numbers*, and `Mathlib/NumberTheory/FLT/Polynomial.lean` only contains
the *polynomial* analogue).  Accordingly this file:

* formalizes the statement (`Frontier.IsCatalanPair`);
* proves *unconditionally* the elementary base cases:
  - equal exponents (`Frontier.not_isCatalanPair_of_eq_exponents`),
  - base `2` on the left (`Frontier.not_isCatalanPair_two_left`): `2 ^ p` is never one more
    than a perfect power,
  - base `2` on the right (`Frontier.isCatalanPair_two_right`): the only perfect power that
    is one more than a power of two is `9 = 2 ^ 3 + 1`;
* proves a Lean-checked **reduction** (`Frontier.Catalan_Mihailescu`) of the full statement,
  for arbitrary exponents `> 1`, to the genuinely deep *core case* `Frontier.CatalanCoreCase`:
  distinct **prime** exponents and both bases `≥ 3`.
-/

namespace Frontier

/-- `IsCatalanPair x p y q` says that `x ^ p - y ^ q = 1`, where all four of
`x, y, p, q` are `> 1`; i.e. `x ^ p` and `y ^ q` are consecutive perfect powers. -/

theorem exponent_eq_one_of_pow_lt_four {x k c : ℕ} (hx : 1 < x) (hc : 1 < c) (hc4 : c < 4)
    (h : x ^ k = c) : k = 1 ∧ x = c := by
  rcases k with _ | _ | k
  · simp at h; omega
  · simpa using h
  · exfalso
    have h1 : 2 ^ (k + 1 + 1) ≤ x ^ (k + 1 + 1) := Nat.pow_le_pow_left hx _
    have h2 : (4 : ℕ) ≤ 2 ^ (k + 1 + 1) := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (k + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

/-- If `x ≥ 3` is odd, `p` is odd and `x ^ p - 1` is a power of two, then `p = 1`.
The point is that `(x ^ p - 1) / (x - 1) = ∑ i < p, x ^ i` is odd, hence equal to `1`. -/
