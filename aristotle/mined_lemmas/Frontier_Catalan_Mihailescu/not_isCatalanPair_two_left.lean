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

theorem not_isCatalanPair_two_left (p y q : ℕ) : ¬ IsCatalanPair 2 p y q := by
  rintro ⟨-, hp, hy, hq, h⟩
  have h2p : (2 : ℕ) ^ p % 2 = 0 := by
    have : (2 : ℕ) ^ p = 2 * 2 ^ (p - 1) := by rw [← pow_succ']; congr 1; omega
    omega
  have hyo : Odd y := by
    rw [Nat.odd_iff]
    by_contra hc
    have hey : Even y := Nat.even_iff.2 (by omega)
    have : Even (y ^ q) := Nat.even_pow.2 ⟨hey, by omega⟩
    rw [Nat.even_iff] at this
    omega
  have hy3 : 3 ≤ y := by rcases hyo with ⟨m, hm⟩; omega
  rcases Nat.even_or_odd q with ⟨k, hk⟩ | hqo
  · -- `q` even: `(y ^ k) ^ 2 + 1 ≡ 2 [MOD 4]`, but `4 ∣ 2 ^ p`.
    have hz : (y ^ k) ^ 2 + 1 = 2 ^ p := by
      rw [← pow_mul, show k * 2 = q by omega]; omega
    obtain ⟨m, hm⟩ : Odd (y ^ k) := hyo.pow
    have h4 : 2 ^ p = 4 * 2 ^ (p - 2) := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
      congr 1; omega
    have hexp : (y ^ k) ^ 2 + 1 = 4 * (m * m + m) + 2 := by rw [hm]; ring
    omega
  · have := odd_pow_add_one_two_pow (n := p) hy3 hyo hqo (by omega)
    omega

/-- **Base `2` on the right**: the only perfect power that is one more than a power of two
(with all exponents `> 1`) is `9 = 2 ^ 3 + 1`. -/
