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

theorem sin_pi_lower (u : ℝ) (h : |u| ≤ 5 / 8) : (6 / 5) * |u| ≤ |Real.sin (Real.pi * u)| := by
  rcases le_total 0 u with hu | hu
  · rw [abs_of_nonneg hu] at h ⊢
    exact sin_pi_lower_nonneg u hu h
  · rw [abs_of_nonpos hu] at h ⊢
    have := sin_pi_lower_nonneg (-u) (by linarith) h
    rwa [show Real.pi * -u = -(Real.pi * u) by ring, Real.sin_neg, abs_neg] at this

/-- Lower bound for the norm of a geometric sum of `A` powers of `e^{2πit}`,
valid as long as the total phase `A t` stays below `5/8`. -/
