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

theorem integral_inv_sq_add (a : ℝ) (ha : 0 < a) :
    ∫ t in Ioi (0 : ℝ), (t ^ 2 + a ^ 2)⁻¹ = π / (2 * a) := by
  obtain ⟨hd, ht⟩ := hasDerivAt_arctan_div a ha
  have := integral_Ioi_of_hasDerivAt_of_nonneg' hd (fun x _ => by positivity) ht
  rw [this]
  simp [div_div]

/-- The `t`-side integral: `∫_0^∞ (32/(t²+16) - 8/(t²+4)) dt = 2π`. -/
