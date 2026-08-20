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

lemma integrableOn_two_div_sq_add_four :
    IntegrableOn (fun t : ℝ => 2 / (t ^ 2 + 4)) (Ioi 0) :=
  MeasureTheory.integrableOn_Ioi_deriv_of_nonneg'
    (fun t _ => hasDerivAt_arctan_half t) (fun t _ => by positivity) tendsto_arctan_half

/-! ### Tonelli and conclusion -/

/-- The half-line version: `∫_0^∞ (sin x / x)² dx = π/2`, obtained from Tonelli's theorem
applied to the kernel `sincKer`. -/
