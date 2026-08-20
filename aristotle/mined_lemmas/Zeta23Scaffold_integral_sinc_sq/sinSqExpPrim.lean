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

noncomputable def sinSqExpPrim (t x : ℝ) : ℝ :=
  Real.exp (-(t * x)) * (-1 / 2 - t * (-t * Real.cos (2 * x) + 2 * Real.sin (2 * x)) / (2 * (t ^ 2 + 4)))

