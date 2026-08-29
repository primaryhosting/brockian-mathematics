/-
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Real MeasureTheory
open scoped Topology BigOperators Classical

namespace Math2

/-! ## The Sato–Tate distribution -/

/-- The Sato–Tate density `(2/π) sin²θ` on `[0, π]`. -/

lemma abs_integral_le_of_bound {u : ℝ → ℝ} {M : ℝ} (hu' : Continuous u)
    (hu : ∀ x ∈ Set.Icc (0:ℝ) π, |u x| ≤ M) :
    |∫ x in (0:ℝ)..π, u x * stDensity x| ≤ M := by
  have hpi : (0:ℝ) < π := Real.pi_pos
  have h1 : |∫ x in (0:ℝ)..π, u x * stDensity x| ≤ ∫ x in (0:ℝ)..π, |u x * stDensity x| :=
    intervalIntegral.abs_integral_le_integral_abs hpi.le
  have h2 : (∫ x in (0:ℝ)..π, |u x * stDensity x|) ≤ ∫ x in (0:ℝ)..π, M * stDensity x := by
    refine intervalIntegral.integral_mono_on hpi.le
      (((hu'.mul continuous_stDensity).abs).intervalIntegrable _ _)
      ((continuous_const.mul continuous_stDensity).intervalIntegrable _ _) ?_
    intro x hx
    rw [abs_mul, abs_of_nonneg (stDensity_nonneg x)]
    exact mul_le_mul_of_nonneg_right (hu x hx) (stDensity_nonneg x)
  have h3 : (∫ x in (0:ℝ)..π, M * stDensity x) = M := by
    rw [intervalIntegral.integral_const_mul, integral_stDensity]
    simp [stCDF, Real.sin_two_pi, Real.pi_ne_zero]
  linarith

/-- The Weyl criterion: if all the Chebyshev (symmetric power) moments tend to zero, then the
angles are equidistributed with respect to the Sato–Tate measure, tested against arbitrary
continuous functions. -/
