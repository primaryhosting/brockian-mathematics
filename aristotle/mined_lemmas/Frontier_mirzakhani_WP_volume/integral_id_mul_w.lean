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

theorem integral_id_mul_w : (∫ u in Ioi (0:ℝ), u * w u) = π ^ 2 / 3 := by
  have h := integral_comp_mul_left_Ioi (fun u : ℝ => u * w u) 0 (by norm_num : (0:ℝ) < 2)
  simp only [mul_zero, smul_eq_mul] at h
  have h2 : (∫ x in Ioi (0:ℝ), (2 * x) * w (2 * x)) = 2 * (π ^ 2 / 12) := by
    have hpt : ∀ x : ℝ, (2 * x) * w (2 * x) = 2 * (x / (1 + rexp x)) := by
      intro x
      simp only [w]
      rw [show (2 * x) / 2 = x by ring]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi (fun x _ => hpt x), integral_const_mul,
      integral_id_div_one_add_exp]
  rw [h2] at h
  linarith [h]

