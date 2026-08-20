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

lemma hasDerivAt_arctan_half (t : ℝ) :
    HasDerivAt (fun t : ℝ => Real.arctan (t / 2)) (2 / (t ^ 2 + 4)) t := by
  have h1 : HasDerivAt (fun t : ℝ => t / 2) (1 / 2 : ℝ) t := by
    simpa using (hasDerivAt_id t).div_const 2
  refine h1.arctan.congr_deriv ?_
  have h2 : (t / 2) ^ 2 + 1 > 0 := by positivity
  field_simp
  ring

