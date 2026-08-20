import Mathlib

/-!
# Integral Sinc Sq
Category: C Integral
Target: Zeta23Scaffold.integral_sinc_sq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Set Filter Real
open scoped Topology ENNReal

namespace Zeta23Scaffold

/-- The auxiliary kernel `t * sin x ^ 2 * exp (-(t * x))`, used to compute the integral of
`(sin x / x) ^ 2` by Tonelli's theorem, via `1 / x ^ 2 = ∫ t in (0, ∞), t * exp (-(t * x))`. -/

lemma integral_t_mul_exp {x : ℝ} (hx : 0 < x) :
    ∫ t in Ioi (0 : ℝ), t * Real.exp (-(t * x)) = 1 / x ^ 2 := by
  have h := MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg'
    (fun t _ => hasDerivAt_tExpPrim hx t) nonneg_t_mul_exp (tendsto_tExpPrim hx)
  rw [h]
  simp [tExpPrim]

