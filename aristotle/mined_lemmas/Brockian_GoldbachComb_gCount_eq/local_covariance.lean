/-
  Brockian/GoldbachComb.lean — THE GOLDBACH COMB CAMPAIGN (July 30).

  The exact local covariance kernel behind the 3|k autocorrelation comb
  of the Goldbach residual (Volume II, page XVI; Tomography §4).

  Chain: local count g_p(c) = p−2+[c=0]  →  centered spike 1_{c=0}−1/p
  →  two-case covariance  →  CRT product over squarefree wheels  →
  convergent global kernel K(h) with  K(h)−1 > 0 ⟺ 3 ∣ h  (the p=3
  factor 9/8 vs 15/16 dominates all higher primes combined).

  Empirical status (this program, recorded): kernel verified exactly at
  p = 3,5,7,11; global values K−1 = +0.1195 / −0.0671; transfer pilot
  against the measured 50-lag ACF: one fitted scale β ≈ 0.41, held-out
  sign agreement 25/25, correlation r = 0.996. The TRANSFER conjecture
  is named at the end and never claimed.

  Charter as Core.lean; each unproved declaration was supplied as a target.
-/
import Mathlib

set_option autoImplicit false

namespace Brockian.GoldbachComb

open Finset

/-- The local Goldbach count: ordered pairs of nonzero residues summing
to c. -/

theorem local_covariance (p : ℕ) [Fact p.Prime] (h : ZMod p) :
    (∑ c : ZMod p, (gCount p c : ℚ) * gCount p (c + h)) / p
      = ((p - 1)^2 / p)^2 * Kp p (if h = 0 then 0 else 1) := by
  haveI : Fact (Nat.Prime p) := ‹_›
  have hp : p.Prime := Fact.out
  have hp_pos : 0 < p := hp.pos
  have hp_ne : p ≠ 1 := hp.ne_one
  -- We'll split into cases h = 0 and h ≠ 0
  by_cases hh : h = 0
  · -- Case h = 0
    simp [hh, Kp]
    -- Rewrite gCount using gCount_eq
    have hg : ∀ x : ZMod p, (gCount p x : ℚ) = if x = 0 then (p : ℚ) - 1 else (p : ℚ) - 2 := by
      intro x
      rw [gCount_eq]
      simp [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_sub (by omega : 2 ≤ p)]
    simp_rw [hg]
    -- Simplify the product of if-then-else statements
    have hsimp : ∀ x : ZMod p, (if x = 0 then (p : ℚ) - 1 else (p : ℚ) - 2) * (if x = 0 then (p : ℚ) - 1 else (p : ℚ) - 2) =
        if x = 0 then ((p : ℚ) - 1)^2 else ((p : ℚ) - 2)^2 := by
      intro x
      by_cases hx : x = 0 <;> simp [hx, sq]
    simp_rw [hsimp]
    -- Split the sum: x = 0 term and x ≠ 0 terms
    have hsplit : ∑ x : ZMod p, (if x = 0 then ((p : ℚ) - 1)^2 else ((p : ℚ) - 2)^2) =
        ((p : ℚ) - 1)^2 + (p - 1) * ((p : ℚ) - 2)^2 := by
      have hcard : Fintype.card (ZMod p) = p := ZMod.card p
      have h1 : ∑ x : ZMod p, (if x = 0 then ((p : ℚ) - 1)^2 else ((p : ℚ) - 2)^2) =
          ∑ x : ZMod p, (if x = 0 then ((p : ℚ) - 1)^2 - ((p : ℚ) - 2)^2 else 0) + ∑ x : ZMod p, ((p : ℚ) - 2)^2 := by
        rw [← Finset.sum_add_distrib]
        congr 1; ext x; by_cases hx : x = 0 <;> simp [hx]
      rw [h1]
      rw [Finset.sum_ite_eq' Finset.univ 0]
      simp [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
      ring_nf
    rw [hsplit]
    have hp1 : (p : ℚ) - 1 ≠ 0 := by
      linarith [show (p : ℚ) > 1 by exact_mod_cast hp.one_lt]
    have hp1_3 : ((p : ℚ) - 1) ^ 3 ≠ 0 := pow_ne_zero 3 hp1
    field_simp
    ring_nf
  · -- Case h ≠ 0
    simp [hh, Kp]
    have hp1 : ¬(p : ℤ) ∣ 1 := by
      intro hdiv
      have : (p : ℤ) ≤ 1 := Int.le_of_dvd (by norm_num) hdiv
      norm_cast at this
      exact hp_ne (le_antisymm this hp_pos)
    simp [hp1]
    -- Rewrite gCount using gCount_eq
    have hg : ∀ x : ZMod p, (gCount p x : ℚ) = if x = 0 then (p : ℚ) - 1 else (p : ℚ) - 2 := by
      intro x
      rw [gCount_eq]
      simp [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_sub (by omega : 2 ≤ p)]
    simp_rw [hg]
    -- Simplify the product of if-then-else statements
    have hsimp : ∀ x : ZMod p, (if x = 0 then (p : ℚ) - 1 else (p : ℚ) - 2) * (if x + h = 0 then (p : ℚ) - 1 else (p : ℚ) - 2) =
        if x = 0 then ((p : ℚ) - 1) * ((p : ℚ) - 2) else
          if x = -h then ((p : ℚ) - 2) * ((p : ℚ) - 1) else ((p : ℚ) - 2)^2 := by
      intro x
      by_cases hx0 : x = 0
      · simp [hx0, hh]
      · by_cases hxh : x = -h
        · simp [hxh, neg_add_cancel, hh]
        · have h2 : ¬x + h = 0 := by
            intro hc
            have := add_eq_zero_iff_eq_neg.mp hc
            exact hxh this
          simp [hx0, hxh, h2, sq]
    simp_rw [hsimp]
    -- Compute the sum over three cases: x = 0, x = -h, and x ≠ 0, x ≠ -h
    have hcard : Fintype.card (ZMod p) = p := ZMod.card p
    have hsplit : ∑ x : ZMod p, (if x = 0 then ((p : ℚ) - 1) * ((p : ℚ) - 2) else if x = -h then ((p : ℚ) - 2) * ((p : ℚ) - 1) else ((p : ℚ) - 2)^2) =
        ((p : ℚ) - 1) * ((p : ℚ) - 2) + ((p : ℚ) - 2) * ((p : ℚ) - 1) + (p - 2) * ((p : ℚ) - 2)^2 := by
      -- Split the sum
      have h1 : ∑ x : ZMod p, (if x = 0 then ((p : ℚ) - 1) * ((p : ℚ) - 2) else if x = -h then ((p : ℚ) - 2) * ((p : ℚ) - 1) else ((p : ℚ) - 2)^2) =
          ∑ x : ZMod p, (if x = 0 then (((p : ℚ) - 1) * ((p : ℚ) - 2) - ((p : ℚ) - 2)^2) else 0) +
          ∑ x : ZMod p, (if x = -h then (((p : ℚ) - 2) * ((p : ℚ) - 1) - ((p : ℚ) - 2)^2) else 0) +
          ∑ x : ZMod p, (((p : ℚ) - 2)^2) := by
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        congr 1; ext x
        by_cases hx0 : x = 0 <;> by_cases hxh : x = -h <;> simp [hx0, hxh, hh]
      rw [h1]
      rw [Finset.sum_ite_eq' Finset.univ 0, Finset.sum_ite_eq' Finset.univ (-h)]
      simp [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
      ring_nf
    rw [hsplit]
    have hp1 : (p : ℚ) - 1 ≠ 0 := by
      linarith [show (p : ℚ) > 1 by exact_mod_cast hp.one_lt]
    have hp1_4 : ((p : ℚ) - 1) ^ 4 ≠ 0 := pow_ne_zero 4 hp1
    have hp_ne : (p : ℚ) ≠ 0 := by
      norm_cast
      exact hp.ne_zero
    field_simp
    ring_nf
-- (the Int-shift phrasing: p ∣ h ↔ the ZMod image of h is 0)

/-
The originally supplied `wheel_kernel` target is retained below, but
commented out because it is not a well-formed or correct theorem.

* It lacks the hypotheses needed to construct the displayed finite types.
* `dvd_of_mem_primeFactors` is not a declaration in this Mathlib version.
* Most importantly, its left side contains only one wheel weight and no
  shifted second factor, so it is a mean rather than an autocorrelation.
  Even under the evident typing repairs, at `M = 3` and `h = 0` its two
  sides would be `4/3` and `(4/3) * (9/8) = 3/2`.

A faithful normalized CRT statement needs a definition of the normalized
wheel weight and a product `W_M(c) * W_M(c+h)` on the left.

/-- GC-4 (original target, invalid). -/
