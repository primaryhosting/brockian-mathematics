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

theorem integrableOn_affine_mul_w_shift (a c d s : ℝ) :
    IntegrableOn (fun u => (c * u + d) * w (u + s)) (Ioi a) := by
  refine integrable_of_isBigO_exp_neg (b := 1/4) (by norm_num) ?_ ?_
  · exact Continuous.continuousOn
      (((continuous_const.mul continuous_id).add continuous_const).mul
        (continuous_w.comp (continuous_id.add continuous_const)))
  · rw [Asymptotics.isBigO_iff]
    refine ⟨rexp (-(s/2)) * (4 * |c| + |d|), ?_⟩
    filter_upwards [Filter.eventually_ge_atTop (0:ℝ)] with u hu
    have hw : w (u + s) ≤ rexp (-(s/2)) * rexp (-(u/2)) := by
      have := w_le_exp (u + s)
      rw [← Real.exp_add] at *
      calc w (u + s) ≤ rexp (-((u + s)/2)) := w_le_exp (u + s)
        _ = rexp (-(s/2) + -(u/2)) := by ring_nf
    have hwpos := (w_pos (u + s)).le
    have h1 : |(c * u + d) * w (u + s)| ≤ (|c| * u + |d|) * (rexp (-(s/2)) * rexp (-(u/2))) := by
      rw [abs_mul, abs_of_nonneg hwpos]
      have hle : |c * u + d| ≤ |c| * u + |d| := by
        calc |c * u + d| ≤ |c * u| + |d| := abs_add_le _ _
          _ = |c| * u + |d| := by rw [abs_mul, abs_of_nonneg hu]
      have h2 : (0:ℝ) ≤ |c| * u + |d| := by positivity
      exact mul_le_mul hle hw hwpos h2
    have h3 : (|c| * u + |d|) * rexp (-(u/2)) ≤ (4 * |c| + |d|) * rexp (-(1/4) * u) := by
      have hexp : 1 + u/4 ≤ rexp (u/4) := by
        have := Real.add_one_le_exp (u/4); linarith
      have hkey : |c| * u + |d| ≤ (4 * |c| + |d|) * rexp (u/4) := by
        nlinarith [abs_nonneg c, abs_nonneg d]
      have hpos : (0:ℝ) < rexp (-(u/2)) := Real.exp_pos _
      calc (|c| * u + |d|) * rexp (-(u/2)) ≤ ((4 * |c| + |d|) * rexp (u/4)) * rexp (-(u/2)) :=
            mul_le_mul_of_nonneg_right hkey hpos.le
        _ = (4 * |c| + |d|) * rexp (-(1/4) * u) := by
            rw [mul_assoc, ← Real.exp_add]; ring_nf
    have hnorm : ‖rexp (-(1/4) * u)‖ = rexp (-(1/4) * u) :=
      Real.norm_of_nonneg (Real.exp_pos _).le
    rw [hnorm, Real.norm_eq_abs]
    have hspos : (0:ℝ) < rexp (-(s/2)) := Real.exp_pos _
    calc |(c * u + d) * w (u + s)| ≤ (|c| * u + |d|) * (rexp (-(s/2)) * rexp (-(u/2))) := h1
      _ = rexp (-(s/2)) * ((|c| * u + |d|) * rexp (-(u/2))) := by ring
      _ ≤ rexp (-(s/2)) * ((4 * |c| + |d|) * rexp (-(1/4) * u)) := by
          exact mul_le_mul_of_nonneg_left h3 hspos.le
      _ = rexp (-(s/2)) * (4 * |c| + |d|) * rexp (-(1/4) * u) := by ring

/-- Any affine multiple of `w` is integrable on a half-line. -/
