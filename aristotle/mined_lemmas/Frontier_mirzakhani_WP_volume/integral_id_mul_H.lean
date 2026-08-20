import Mathlib

/-!
# The Fermi–Dirac integral `∫_0^∞ t/(1+e^t) dt = π²/12`

This auxiliary file establishes the elementary integral underlying Mirzakhani's
integration kernel, via the Mellin transform of the Dirichlet eta function.
-/


open Real MeasureTheory Set Complex
open scoped Real

namespace Mirzakhani

/-- Coefficients of the Dirichlet eta series, with the (irrelevant) `n = 0` term set to `0`. -/

theorem integral_id_mul_H (y : ℝ) :
    (∫ x in Ioi (0:ℝ), x * H x y) = y ^ 2 / 2 + 2 * π ^ 2 / 3 := by
  rcases le_total 0 y with hy | hy
  · exact integral_id_mul_H_of_nonneg hy
  · have h := integral_id_mul_H_of_nonneg (y := -y) (by linarith)
    have hEq : (∫ x in Ioi (0:ℝ), x * H x (-y)) = ∫ x in Ioi (0:ℝ), x * H x y :=
      setIntegral_congr_fun measurableSet_Ioi (fun x _ => by rw [H_symm])
    rw [hEq] at h
    rw [h]; ring

/-- The two-kernel moment integral appearing in the `B` term of Mirzakhani's recursion. -/
