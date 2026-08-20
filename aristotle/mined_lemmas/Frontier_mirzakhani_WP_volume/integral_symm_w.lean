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

lemma integral_symm_w (y : ℝ) : (∫ u in (-y)..y, w u) = y := by
  have hadd := intervalIntegral.integral_add_adjacent_intervals (a := -y) (b := 0) (c := y)
    (intervalIntegrable_w _ _) (intervalIntegrable_w _ _)
  have hneg : (∫ u in (-y)..(0:ℝ), w u) = ∫ x in (0:ℝ)..y, w (-x) := by
    rw [intervalIntegral.integral_comp_neg (fun x => w x)]
    norm_num
  have hval : (∫ x in (0:ℝ)..y, w (-x)) = y - ∫ x in (0:ℝ)..y, w x := by
    have h1 : (∫ x in (0:ℝ)..y, w (-x)) = ∫ x in (0:ℝ)..y, (1 - w x) :=
      intervalIntegral.integral_congr (fun x _ => w_neg x)
    rw [h1, intervalIntegral.integral_sub (_root_.intervalIntegrable_const)
      (intervalIntegrable_w _ _)]
    simp
  rw [hneg, hval] at hadd
  linarith

