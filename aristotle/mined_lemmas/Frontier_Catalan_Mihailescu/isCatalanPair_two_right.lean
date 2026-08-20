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

theorem isCatalanPair_two_right (x p q : ℕ) (h : IsCatalanPair x p 2 q) :
    x = 3 ∧ p = 2 ∧ q = 3 := by
  obtain ⟨hx, hp, -, hq, h⟩ := h
  have h2q : (2 : ℕ) ^ q % 2 = 0 := by
    have : (2 : ℕ) ^ q = 2 * 2 ^ (q - 1) := by rw [← pow_succ']; congr 1; omega
    omega
  have hxo : Odd x := by
    rw [Nat.odd_iff]
    by_contra hc
    have hex : Even x := Nat.even_iff.2 (by omega)
    have : Even (x ^ p) := Nat.even_pow.2 ⟨hex, by omega⟩
    rw [Nat.even_iff] at this
    omega
  have hx3 : 3 ≤ x := by rcases hxo with ⟨m, hm⟩; omega
  rcases Nat.even_or_odd p with ⟨k, hk⟩ | hpo
  · -- `p` even: `u = x ^ k` satisfies `(u - 1) (u + 1) = 2 ^ q`, forcing `u = 3`.
    have hk1 : 1 ≤ k := by omega
    have hu : (x ^ k) ^ 2 = 2 ^ q + 1 := by
      rw [← pow_mul, show k * 2 = p by omega]; exact h
    obtain ⟨m, hm⟩ : Odd (x ^ k) := hxo.pow
    have hxk3 : 3 ≤ x ^ k := le_trans hx3 (Nat.le_self_pow (by omega) x)
    have hfac : 4 * (m * (m + 1)) = 2 ^ q := by
      have h1 : (x ^ k) ^ 2 = 4 * (m * m + m) + 1 := by rw [hm]; ring
      have h2 : 4 * (m * (m + 1)) = 4 * (m * m + m) := by ring
      omega
    have hdm : m ∣ 2 ^ q := ⟨4 * (m + 1), by rw [← hfac]; ring⟩
    have hdm1 : (m + 1) ∣ 2 ^ q := ⟨4 * m, by rw [← hfac]; ring⟩
    have hmodd : Odd m := by
      rcases Nat.even_or_odd m with he | ho
      · exact absurd (eq_one_of_odd_of_dvd_two_pow (Even.add_one he) hdm1) (by omega)
      · exact ho
    have hm1 : m = 1 := eq_one_of_odd_of_dvd_two_pow hmodd hdm
    subst hm1
    have hq3 : q = 3 := Nat.pow_right_injective (le_refl 2) (show 2 ^ q = 2 ^ 3 by omega)
    obtain ⟨hk1', hx3'⟩ :=
      exponent_eq_one_of_pow_lt_four hx (c := 3) (by norm_num) (by norm_num) (by omega)
    exact ⟨hx3', by omega, hq3⟩
  · exact absurd (odd_pow_sub_one_two_pow (n := q) hx3 hxo hpo h) (by omega)

/-! ### Reduction to the core case -/

/-- The *core case* of Catalan's conjecture: there is no solution of `x ^ p = y ^ q + 1` with
distinct prime exponents `p ≠ q` and both bases at least `3`.  This is the part of
Mihailescu's theorem that is not elementary. -/
