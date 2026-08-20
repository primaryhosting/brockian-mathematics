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

lemma integrableOn_sincKer_x {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun x : ℝ => sincKer x t) (Ioi 0) :=
  MeasureTheory.integrableOn_Ioi_deriv_of_nonneg'
    (fun x _ => hasDerivAt_sinSqExpPrim t x)
    (fun _ _ => sincKer_nonneg ht.le) (tendsto_sinSqExpPrim ht)

/-! ### The outer integral -/

