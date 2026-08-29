/-
# Integral Sinc Fourth
Category: C Integral
Target: Zeta23Scaffold.integral_sinc_fourth
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Integral Sinc Fourth
Category: C Integral
Target: Zeta23Scaffold.integral_sinc_fourth
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Zeta23Scaffold

open MeasureTheory Set Real Filter Topology

/-! ### Laplace transform of `cos (a * x)` on `(0, ∞)` -/

/-- The function `x ↦ e^{-t x} cos (a x)` is integrable on `(0, ∞)` when `t > 0`. -/

theorem sincAux_integrable_prod :
    Integrable (Function.uncurry sincAux)
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) := by
  have hmeas : AEStronglyMeasurable (Function.uncurry sincAux)
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) := by
    apply Continuous.aestronglyMeasurable
    unfold Function.uncurry sincAux
    fun_prop
  rw [MeasureTheory.integrable_prod_iff' hmeas]
  constructor
  · refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall ?_)
    intro t ht
    exact sincAux_integrableOn_x t ht
  · have hint : IntegrableOn
        (fun t : ℝ => 32 * ((t ^ 2 + 4 ^ 2)⁻¹) - 8 * ((t ^ 2 + 2 ^ 2)⁻¹)) (Ioi 0) :=
      ((integrableOn_inv_sq_add 4 (by norm_num)).const_mul _).sub
        ((integrableOn_inv_sq_add 2 (by norm_num)).const_mul _)
    refine hint.congr ?_
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall ?_)
    intro t ht
    exact (integral_norm_sincAux t ht).symm

/-- The key half-line evaluation: `∫_0^∞ sin⁴x / x⁴ dx = π/3`. -/
