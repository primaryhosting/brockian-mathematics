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

lemma integral_two_div_sq_add_four :
    ∫ t in Ioi (0 : ℝ), 2 / (t ^ 2 + 4) = π / 2 := by
  have h := MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg' (a := 0)
    (fun t _ => hasDerivAt_arctan_half t) (fun t (_ : t ∈ Ioi (0:ℝ)) => by positivity)
    tendsto_arctan_half
  simpa using h

