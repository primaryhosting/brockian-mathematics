/-
The quantum period-finding subroutine: the state produced by the algorithm,
the measurement distribution of the first register, and the lower bound on the
probability of a "good" measurement outcome.
-/
import Mathlib
import RequestProject.Analysis

open scoped BigOperators
open scoped Real
open scoped Classical

set_option maxHeartbeats 2000000

namespace QI

/-- The primitive `Q`-th root of unity `e^{2πi/Q}` used by the quantum Fourier transform. -/

theorem sin_pi_lower_nonneg (u : ℝ) (hu : 0 ≤ u) (h : u ≤ 5 / 8) :
    (6 / 5) * u ≤ |Real.sin (Real.pi * u)| := by
  have hpi := Real.pi_gt_three
  have hpi4 := Real.pi_le_four
  rcases le_or_gt u (1 / 2) with h1 | h1
  · have h2 : Real.pi * u ≤ Real.pi / 2 := by nlinarith
    have h3 : 0 ≤ Real.pi * u := by positivity
    have hml := Real.mul_le_sin h3 h2
    have hs : 0 ≤ Real.sin (Real.pi * u) :=
      Real.sin_nonneg_of_nonneg_of_le_pi h3 (by nlinarith)
    rw [abs_of_nonneg hs]
    have he : 2 / Real.pi * (Real.pi * u) = 2 * u := by field_simp
    nlinarith
  · have key : Real.sin (Real.pi * u) = Real.sin (Real.pi * (1 - u)) := by
      rw [show Real.pi * (1 - u) = Real.pi - Real.pi * u by ring, Real.sin_pi_sub]
    have h3 : 0 ≤ Real.pi * (1 - u) := by nlinarith
    have h2 : Real.pi * (1 - u) ≤ Real.pi / 2 := by nlinarith
    have hb := Real.mul_le_sin h3 h2
    have he : 2 / Real.pi * (Real.pi * (1 - u)) = 2 * (1 - u) := by field_simp
    rw [key, abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi h3 (by nlinarith))]
    nlinarith

/-- A Jordan-type bound: `|sin (π u)| ≥ (6/5)|u|` for `|u| ≤ 5/8`. -/
