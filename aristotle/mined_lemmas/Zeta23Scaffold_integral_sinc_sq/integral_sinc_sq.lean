import Mathlib

/-!
# Integral Sinc Sq
Category: C Integral
Target: Zeta23Scaffold.integral_sinc_sq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Complex Real
open scoped FourierTransform

namespace Zeta23Scaffold

/-- The triangle ("tent") function `x ↦ max (1 - |x|) 0`, viewed as a complex-valued function. -/

theorem integral_sinc_sq : ∫ x : ℝ, (Real.sin x / x) ^ 2 = π := by
  have hc := Measure.integral_comp_mul_left (fun x : ℝ => (Real.sin x / x) ^ 2) π
  rw [integral_sinc_pi_sq, abs_of_pos (by positivity : (0 : ℝ) < π⁻¹), smul_eq_mul,
    inv_mul_eq_div, eq_div_iff Real.pi_ne_zero, one_mul] at hc
  exact hc.symm

end Zeta23Scaffold

