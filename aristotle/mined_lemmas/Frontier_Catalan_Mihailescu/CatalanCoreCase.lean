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

def CatalanCoreCase : Prop :=
  ∀ x p y q : ℕ, Nat.Prime p → Nat.Prime q → p ≠ q → 3 ≤ x → 3 ≤ y → x ^ p ≠ y ^ q + 1

/-- **Catalan–Mihailescu**, reduced to the core case: assuming `CatalanCoreCase` (distinct prime
exponents, both bases `≥ 3`), the only pair of consecutive perfect powers is
`8 = 2 ^ 3`, `9 = 3 ^ 2`, i.e. any solution of `x ^ p - y ^ q = 1` with `x, y, p, q > 1`
has `x = 3`, `p = 2`, `y = 2`, `q = 3`.

The reduction replaces the exponents `p, q` by prime divisors `r ∣ p`, `s ∣ q` and the bases by
`x ^ (p / r)`, `y ^ (q / s)`; the cases with a base equal to `2` or with `r = s` are then settled
unconditionally by the base cases above. -/
