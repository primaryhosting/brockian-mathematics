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

theorem integral_lorentz_combo :
    ∫ t in Ioi (0 : ℝ), (32 * ((t ^ 2 + 4 ^ 2)⁻¹) - 8 * ((t ^ 2 + 2 ^ 2)⁻¹)) = 2 * π := by
  have h4 : IntegrableOn (fun t : ℝ => 32 * ((t ^ 2 + 4 ^ 2)⁻¹)) (Ioi 0) :=
    (integrableOn_inv_sq_add 4 (by norm_num)).const_mul _
  have h2 : IntegrableOn (fun t : ℝ => 8 * ((t ^ 2 + 2 ^ 2)⁻¹)) (Ioi 0) :=
    (integrableOn_inv_sq_add 2 (by norm_num)).const_mul _
  rw [MeasureTheory.integral_sub h4 h2, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul, integral_inv_sq_add 4 (by norm_num),
    integral_inv_sq_add 2 (by norm_num)]
  ring

/-! ### The Fubini argument -/

/-- The two-variable integrand. -/
