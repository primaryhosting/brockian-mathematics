import Mathlib

/-!
# Legendre's three-square theorem

A natural number `n` is a sum of three squares if and only if it is not of the
form `4 ^ a * (8 * b + 7)`.

The proof is self-contained (only core `Mathlib` is used).  The hard direction
goes through the classical route:

* Minkowski's convex body theorem shows that every positive definite integral
  ternary quadratic form of determinant one represents `1`, hence (by descent)
  is of the shape `Nᵀ * N`.
* Dirichlet's theorem on primes in arithmetic progressions together with
  quadratic reciprocity produces, for every `n` with `n % 4 ≠ 0` and
  `n % 8 ≠ 7`, an integer `m > 0` with `n ∣ m + 1` and `-n` a square modulo `m`.
  Out of these data one builds an explicit positive definite integral ternary
  form of determinant one whose `(0,0)` entry is `n`.
-/

namespace Brockian.LegendreThreeSquare

open Matrix MeasureTheory
open scoped ENNReal

/-! ## Integral quadratic forms -/

/-- The value at `v` of the quadratic form attached to the integer matrix `A`. -/

theorem volume_ellipsoid3 :
    (8 : ℝ≥0∞) < volume {x : Fin 3 → ℝ | ∑ i, (x i) ^ 2 < 19 / 10} := by
  have hr : (0 : ℝ) < Real.sqrt (19 / 10) := Real.sqrt_pos.mpr (by norm_num)
  have hsq : Real.sqrt (19 / 10) ^ 2 = 19 / 10 := Real.sq_sqrt (by norm_num)
  have hset : {x : Fin 3 → ℝ | ∑ i, (x i) ^ 2 < 19 / 10}
      = {x : Fin 3 → ℝ | (∑ i, |x i| ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) < Real.sqrt (19 / 10)} := by
    rw [← ball_set_eq 3 _ hr, hsq]
  rw [hset, MeasureTheory.volume_sum_rpow_lt (Fin 3) (by norm_num)]
  simp only [Fintype.card_fin]
  have g1 : Real.Gamma (1 / (2 : ℝ) + 1) = Real.sqrt Real.pi / 2 := by
    rw [Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]; ring
  have g2 : Real.Gamma (((3 : ℕ) : ℝ) / 2 + 1) = 3 * Real.sqrt Real.pi / 4 := by
    rw [show (((3 : ℕ) : ℝ) / 2 + 1) = (1 / 2 + 1) + 1 by norm_num,
      Real.Gamma_add_one (by norm_num), Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]
    ring
  rw [g1, g2]
  have hpi : Real.sqrt Real.pi > 0 := Real.sqrt_pos.mpr Real.pi_pos
  have hsqpi : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
  have hconst : (2 * (Real.sqrt Real.pi / 2)) ^ 3 / (3 * Real.sqrt Real.pi / 4)
      = 4 * Real.pi / 3 := by
    field_simp
    nlinarith [hsqpi, hpi]
  rw [hconst, ← ENNReal.ofReal_pow hr.le, ← ENNReal.ofReal_mul (by positivity),
    show (8 : ℝ≥0∞) = ENNReal.ofReal 8 by simp, ENNReal.ofReal_lt_ofReal_iff (by positivity)]
  set s := Real.sqrt (19 / 10)
  have h3 : s ^ 3 > 2.6 := by nlinarith [Real.sqrt_nonneg (19 / 10 : ℝ)]
  nlinarith [Real.pi_gt_three, h3]

