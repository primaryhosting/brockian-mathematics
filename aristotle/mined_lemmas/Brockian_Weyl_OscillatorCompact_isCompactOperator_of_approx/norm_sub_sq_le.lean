/-
  CompactCriterion.lean — an abstract compactness criterion: an operator whose
  unit-ball image is uniformly approximable by finite-dimensional subspaces is
  a compact operator.
-/
import Mathlib

open Metric Filter

namespace Brockian.Weyl.OscillatorCompact

/-- An operator whose closed-unit-ball image is uniformly approximable by
finite-dimensional subspaces is a compact operator. -/

theorem norm_sub_sq_le (g : SchwartzMap ℝ ℂ) {y x : ℝ} (hyx : y ≤ x) :
    ‖g x - g y‖ ^ 2 ≤ (x - y) * ∫ t in Set.Ioc y x, ‖deriv (g : ℝ → ℂ) t‖ ^ 2 := by
  have hc := deriv_continuous g
  have hftc : ∫ t in y..x, deriv (g : ℝ → ℂ) t = g x - g y := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => ?_)
      (hc.intervalIntegrable _ _)
    exact (g.differentiable.differentiableAt (x := t)).hasDerivAt
  have h1 : ‖g x - g y‖ ≤ ∫ t in y..x, ‖deriv (g : ℝ → ℂ) t‖ := by
    rw [← hftc]; exact intervalIntegral.norm_integral_le_integral_norm hyx
  rw [intervalIntegral.integral_of_le hyx] at h1
  have hm : (volume (Set.Ioc y x)).toReal = x - y := by
    simp [Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ x - y)]
  have hcs := sq_setIntegral_le (I := Set.Ioc y x) (fun t => ‖deriv (g : ℝ → ℂ) t‖)
    hc.norm.integrableOn_Ioc (by simpa using (hc.norm.pow 2).integrableOn_Ioc)
    (by simp [Real.volume_Ioc])
  rw [Measure.real, hm] at hcs
  have h0 : (0:ℝ) ≤ ∫ t in Set.Ioc y x, ‖deriv (g : ℝ → ℂ) t‖ :=
    integral_nonneg fun _ => norm_nonneg _
  nlinarith [norm_nonneg (g x - g y), h1, hcs]

/-- **Cell estimate.** On an interval of length `b − a`, replacing `g` by its
value at the right endpoint costs at most `(b−a)² ∫ ‖g'‖²`. -/
