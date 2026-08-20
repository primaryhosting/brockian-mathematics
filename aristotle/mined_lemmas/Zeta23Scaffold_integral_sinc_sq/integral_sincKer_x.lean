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

lemma integral_sincKer_x {t : ℝ} (ht : 0 < t) :
    ∫ x in Ioi (0 : ℝ), sincKer x t = 2 / (t ^ 2 + 4) := by
  have h := MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg' (a := 0)
    (fun x _ => hasDerivAt_sinSqExpPrim t x)
    (fun x _ => sincKer_nonneg ht.le) (tendsto_sinSqExpPrim ht)
  rw [h]
  have h4 : (t : ℝ) ^ 2 + 4 ≠ 0 := by positivity
  simp only [sinSqExpPrim, mul_zero, neg_zero, Real.exp_zero, one_mul, Real.cos_zero,
    Real.sin_zero]
  field_simp
  ring

