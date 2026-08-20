import Mathlib

/-!
# Ramanujan's partition congruence `p(7n+5) ≡ 0 (mod 7)`

This file contains a self-contained proof of Ramanujan's congruence for the modulus `7`.

The strategy is the classical generating function argument:

* Let `E = ∏ (1 - X^i)` and `P = ∑ p(n) X^n = E⁻¹`.
* Jacobi's identity `E^3 = ∑_{j ≥ 0} (-1)^j (2j+1) X^{j(j+1)/2}` is proved from a finite form of
  the Jacobi triple product, obtained by induction on `n` from the `q`-Pascal recursion for
  Gaussian binomial coefficients, together with a dual-number ("derivative at `z = -1`")
  specialization and a limiting argument.
* In characteristic `7` one has `E^7 = ∏ (1 - X^{7i})`, so `P · E^7 = E^6 = (E^3)^2`, and the
  coefficients of `(E^3)^2` in degrees `≡ 5 (mod 7)` vanish mod `7` because `-1` is not a square
  mod `7`.
* A strong induction then gives `7 ∣ p(7n+5)`.
-/

namespace Brockian.Ramanujan7

open Finset PowerSeries
open scoped PowerSeries.WithPiTopology

/-! ## Gaussian binomial coefficients -/

section QB

variable {R : Type*} [CommRing R]

/-- The Gaussian binomial coefficient `[n choose k]_q`, defined by the `q`-Pascal recursion. -/

lemma cc_rec1 (q : R) (n : ℕ) :
    cc q (n + 1) 1 = (1 + q ^ (2 * n + 1)) * cc q n 0 + q ^ n * cc q n 1 := by
  unfold cc
  rw [ee_shift]
  simp [qb_zero_right]
  -- Goal: q ^ ee n 0 * qb q (2 * (n + 1)) 1 = (1 + q ^ (2 * n + 1)) * q ^ ee n 0 + q ^ n * (q ^ ee n 1 * qb q (2 * n) 1)
  -- Key identity: n + ee n 1 = ee n 0 + 1 (from ee_up and ee_shift)
  have ee_rel : n + ee n 1 = ee n 0 + 1 := by
    have := ee_up n 1
    simp [ee_shift] at this
    linarith
  -- Use qb_succ_succ recurrence: qb q (m+1) 1 = qb q m 0 + q * qb q m 1 = 1 + q * qb q m 1
  have qb1 : ∀ m : ℕ, qb q (m + 1) 1 = 1 + q * qb q m 1 := by
    intro m
    rw [qb_succ_succ]
    simp [qb_zero_right]
  rw [show 2 * (n + 1) = 2 * n + 2 by ring]
  have h2 : qb q (2 * n + 2) 1 = 1 + q * qb q (2 * n + 1) 1 := qb1 (2 * n + 1)
  have h1 : qb q (2 * n + 1) 1 = 1 + q * qb q (2 * n) 1 := qb1 (2 * n)
  rw [h2, h1]
  -- Also need: qb q n 1 = ∑ i ∈ range n, q ^ i
  have qb_q1 : ∀ m : ℕ, qb q m 1 = ∑ i ∈ range m, q ^ i := by
    intro m
    induction m with
    | zero => simp [qb]
    | succ m ih =>
      rw [qb_succ_succ, ih, Finset.range_add_one]
      simp [qb_zero_right]
      linear_combination geom_sum_mul q m
  -- Use geometric series property: (q - 1) * qb q (2*n) 1 = q^(2*n) - 1
  have geo_sum : (q - 1) * qb q (2 * n) 1 = q ^ (2 * n) - 1 := by
    rw [qb_q1]
    rw [mul_comm]
    exact geom_sum_mul q (2 * n)
  -- Use: q ^ n * q ^ ee n 1 = q ^ (ee n 0 + 1) = q * q ^ ee n 0
  have q_prod : q ^ n * q ^ ee n 1 = q ^ ee n 0 * q := by
    have h : n + ee n 1 = ee n 0 + 1 := by linarith
    rw [← pow_add, h, pow_succ', mul_comm]
  have qb_term : q ^ n * (q ^ ee n 1 * qb q (2 * n) 1) = q ^ ee n 0 * q * qb q (2 * n) 1 := by
    rw [← mul_assoc (q ^ n) (q ^ ee n 1), q_prod]
  rw [qb_term]
  linear_combination geo_sum * q ^ (ee n 0 + 1)

