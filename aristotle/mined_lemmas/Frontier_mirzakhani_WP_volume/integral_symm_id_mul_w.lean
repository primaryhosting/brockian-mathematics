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

lemma integral_symm_id_mul_w (y : ℝ) :
    (∫ u in (-y)..y, u * w u) = 2 * (∫ u in (0:ℝ)..y, u * w u) - y ^ 2 / 2 := by
  have hadd := intervalIntegral.integral_add_adjacent_intervals (a := -y) (b := 0) (c := y)
    (intervalIntegrable_id_mul_w _ _) (intervalIntegrable_id_mul_w _ _)
  have hneg : (∫ u in (-y)..(0:ℝ), u * w u) = ∫ x in (0:ℝ)..y, (-x) * w (-x) := by
    rw [intervalIntegral.integral_comp_neg (fun x => x * w x)]
    norm_num
  have hval : (∫ x in (0:ℝ)..y, (-x) * w (-x)) = (∫ x in (0:ℝ)..y, x * w x) - y ^ 2 / 2 := by
    have h1 : (∫ x in (0:ℝ)..y, (-x) * w (-x)) = ∫ x in (0:ℝ)..y, (x * w x - x) := by
      refine intervalIntegral.integral_congr (fun x _ => ?_)
      rw [w_neg]
      ring
    rw [h1, intervalIntegral.integral_sub (intervalIntegrable_id_mul_w _ _)
      (intervalIntegral.intervalIntegrable_id), integral_id]
    ring_nf
  rw [hneg, hval] at hadd
  linarith

