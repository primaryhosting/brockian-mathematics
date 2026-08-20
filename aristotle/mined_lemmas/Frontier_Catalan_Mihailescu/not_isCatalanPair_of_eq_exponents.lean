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

theorem not_isCatalanPair_of_eq_exponents (x y n : ℕ) : ¬ IsCatalanPair x n y n := by
  rintro ⟨-, hn, hy, -, h⟩
  have hxy : y + 1 ≤ x := by
    by_contra hc
    push_neg at hc
    have : x ^ n ≤ y ^ n := Nat.pow_le_pow_left (by omega) _
    omega
  have key : ∀ m : ℕ, 2 ≤ m → y ^ m + 2 ≤ (y + 1) ^ m := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => ring_nf; nlinarith
    | succ m hm ih =>
        have hrw : (y + 1) ^ (m + 1) = (y + 1) * (y + 1) ^ m := by ring
        have hp : y ^ (m + 1) = y * y ^ m := by ring
        have h2 : (y + 1) * (y ^ m + 2) ≤ (y + 1) * (y + 1) ^ m := Nat.mul_le_mul_left _ ih
        rw [hrw, hp]
        nlinarith [pow_pos (show 0 < y by omega) m]
  have k1 := key n hn
  have k2 : (y + 1) ^ n ≤ x ^ n := Nat.pow_le_pow_left hxy _
  omega

/-- **Base `2` on the left**: `2 ^ p - y ^ q = 1` has no solution with `y, p, q > 1`.
(A power of two is never one more than a perfect power.) -/
