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

lemma hasDerivAt_tExpPrim {x : ℝ} (hx : 0 < x) (t : ℝ) :
    HasDerivAt (tExpPrim x) (t * Real.exp (-(t * x))) t := by
  have hlin : HasDerivAt (fun t : ℝ => -(t * x)) (-x) t := by
    simpa using ((hasDerivAt_id t).mul_const x).neg
  have h1 : HasDerivAt (fun t : ℝ => -(t / x + 1 / x ^ 2)) (-(1 / x)) t := by
    have h0 := (((hasDerivAt_id t).div_const x).add_const (1 / x ^ 2)).neg
    exact h0.congr_deriv (by simp)
  have h3 := h1.mul hlin.exp
  refine h3.congr_deriv ?_
  have hx' : x ≠ 0 := ne_of_gt hx
  field_simp
  ring

