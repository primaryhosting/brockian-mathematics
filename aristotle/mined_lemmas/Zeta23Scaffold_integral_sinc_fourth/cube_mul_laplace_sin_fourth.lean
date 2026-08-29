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

theorem cube_mul_laplace_sin_fourth (t : ℝ) (ht : 0 < t) :
    t ^ 3 * (3 / (8 * t) - t / (2 * (t ^ 2 + 4)) + t / (8 * (t ^ 2 + 16)))
      = 32 * ((t ^ 2 + 4 ^ 2)⁻¹) - 8 * ((t ^ 2 + 2 ^ 2)⁻¹) := by
  have h1 : t ≠ 0 := ne_of_gt ht
  have h2 : t ^ 2 + 4 ≠ 0 := by positivity
  have h3 : t ^ 2 + 16 ≠ 0 := by positivity
  norm_num
  field_simp
  ring

/-! ### The Gamma-type integral `∫_0^∞ t³ e^{-x t} dt` -/

