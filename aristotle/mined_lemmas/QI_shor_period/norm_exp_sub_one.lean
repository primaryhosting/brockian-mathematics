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

theorem norm_exp_sub_one (x : ℝ) :
    ‖Complex.exp ((x : ℂ) * Complex.I) - 1‖ = 2 * |Real.sin (x / 2)| := by
  have h1 : Complex.exp ((x : ℂ) * Complex.I) - 1 = ⟨Real.cos x - 1, Real.sin x⟩ := by
    rw [Complex.exp_mul_I]
    simp [Complex.ext_iff, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have hx : Real.cos (2 * (x / 2)) = 2 * Real.cos (x / 2) ^ 2 - 1 := Real.cos_two_mul _
  rw [show 2 * (x / 2) = x by ring] at hx
  have h2 : Real.cos x = 1 - 2 * Real.sin (x / 2) ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq (x / 2)]
  rw [h1, Complex.norm_def, Complex.normSq_mk]
  have h3 : (Real.cos x - 1) * (Real.cos x - 1) + Real.sin x * Real.sin x
      = 4 * Real.sin (x / 2) ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq x, h2]
  rw [h3, show (4 : ℝ) * Real.sin (x / 2) ^ 2 = (2 * |Real.sin (x / 2)|) ^ 2 by
    rw [mul_pow, sq_abs]; ring]
  exact Real.sqrt_sq (by positivity)

