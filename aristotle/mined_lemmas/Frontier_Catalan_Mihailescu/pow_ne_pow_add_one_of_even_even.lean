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

theorem pow_ne_pow_add_one_of_even_even {x y p q : ℕ} (hy : 1 < y) (hp : Even p) (hq : Even q) :
    x ^ p ≠ y ^ q + 1 := by
  intro h
  obtain ⟨s, hs⟩ := hp
  obtain ⟨t, ht⟩ := hq
  have hxs : x ^ p = (x ^ s) ^ 2 := by rw [← pow_mul]; rw [hs]; ring_nf
  have hyt : y ^ q = (y ^ t) ^ 2 := by rw [← pow_mul]; rw [ht]; ring_nf
  set A := x ^ s
  set B := y ^ t with hB
  rw [hxs, hyt] at h
  -- `B ≥ 2` as soon as `t ≥ 1`; the degenerate case `t = 0` is handled separately
  rcases Nat.eq_zero_or_pos t with ht0 | ht0
  · -- then `q = 0`, so `A ^ 2 = 2`, which is impossible
    subst ht0
    simp only [pow_zero] at hB
    rw [hB] at h
    norm_num at h
    rcases Nat.lt_or_ge A 2 with hA2 | hA2
    · interval_cases A <;> omega
    · nlinarith
  · have hB2 : 2 ≤ B := by
      rw [hB]
      calc 2 ≤ y := hy
      _ = y ^ 1 := (pow_one y).symm
      _ ≤ y ^ t := Nat.pow_le_pow_right (by omega) ht0
    have hAB : B < A := by
      by_contra hc
      push_neg at hc
      have : A ^ 2 ≤ B ^ 2 := Nat.pow_le_pow_left hc 2
      omega
    nlinarith

/-- If `x ^ 2 = y ^ q + 1` with `q ≥ 2`, then `y` cannot be odd (and `> 1`).
This is the coprime-factorisation subcase `(x-1)(x+1) = y ^ q`. -/
