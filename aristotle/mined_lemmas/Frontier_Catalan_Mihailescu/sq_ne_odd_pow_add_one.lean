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

theorem sq_ne_odd_pow_add_one {x y q : ℕ} (hyodd : Odd y) (hy : 1 < y) (hq : 2 ≤ q) :
    x ^ 2 ≠ y ^ q + 1 := by
  intro h
  have hyq : 9 ≤ y ^ q := by
    calc (9 : ℕ) = 3 ^ 2 := by norm_num
    _ ≤ y ^ 2 := Nat.pow_le_pow_left (by rcases hyodd with ⟨k, hk⟩; omega) 2
    _ ≤ y ^ q := Nat.pow_le_pow_right (by omega) hq
  have hx : 3 ≤ x := by
    by_contra hc
    push_neg at hc
    interval_cases x <;> omega
  obtain ⟨u, rfl⟩ : ∃ u, x = u + 1 := ⟨x - 1, by omega⟩
  have hprod : u * (u + 2) = y ^ q := by nlinarith [h]
  -- `y ^ q` is odd, hence `(u+1)^2` is even, hence `u` is odd
  have hyqodd : Odd (y ^ q) := hyodd.pow
  have hueven : Even ((u + 1) ^ 2) := by
    rw [h]
    exact hyqodd.add_one
  have hu1 : Even (u + 1) := by
    rcases (Nat.even_pow.mp hueven) with ⟨he, -⟩
    exact he
  have huodd : u % 2 = 1 := by
    have h' := Nat.even_iff.mp hu1
    omega
  have hcop : Nat.Coprime u (u + 2) := by
    have hg : Nat.gcd u (u + 2) = Nat.gcd u 2 := by
      rw [Nat.add_comm u 2, Nat.gcd_add_self_right]
    have h2u : Nat.Coprime 2 u := (Nat.prime_two.coprime_iff_not_dvd).mpr (by omega)
    rw [Nat.Coprime, hg, Nat.gcd_comm]
    exact h2u
  obtain ⟨a, ha⟩ := eq_pow_of_coprime_mul_eq_pow hcop hprod
  obtain ⟨b, hb⟩ := eq_pow_of_coprime_mul_eq_pow hcop.symm (by rw [Nat.mul_comm]; exact hprod)
  -- now `b ^ q = a ^ q + 2` with `a ≥ 2`
  have hu3 : 3 ≤ u := by nlinarith
  have ha2 : 2 ≤ a := by
    by_contra hc
    push_neg at hc
    interval_cases a
    · rw [zero_pow (by omega)] at ha; omega
    · rw [one_pow] at ha; omega
  have hba : a < b := by
    by_contra hc
    push_neg at hc
    have : b ^ q ≤ a ^ q := Nat.pow_le_pow_left hc q
    omega
  have h1 : (a + 1) ^ q ≤ b ^ q := Nat.pow_le_pow_left (by omega) q
  have h2 : a ^ q + q * a ≤ (a + 1) ^ q := succ_pow_lower_bound a q hq
  have h3 : 2 * 2 ≤ q * a := Nat.mul_le_mul hq ha2
  omega

/-- If `x ^ p = y ^ q + 1` with `p` even, `q ≥ 2` and `y > 1`, then `y` is even.
Equivalently: there is no solution with `p` even and `y` odd. -/
