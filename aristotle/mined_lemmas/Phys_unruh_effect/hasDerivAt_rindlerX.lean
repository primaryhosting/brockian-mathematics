/-
/-!
# Unruh Effect
Category: Frontier Phys
Target: Phys.unruh_effect
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/

import Mathlib

/-!
# Unruh Effect
Category: Frontier Phys
Target: Phys.unruh_effect
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open scoped Real

set_option maxHeartbeats 1000000

namespace Phys

/-! ## The Unruh temperature -/

/-- The Unruh temperature `T = ℏ a / (2 π c k_B)` seen by an observer with proper
acceleration `a`. -/

theorem hasDerivAt_rindlerX (a c τ : ℝ) (ha : a ≠ 0) (hc : c ≠ 0) :
    HasDerivAt (rindlerX a c) (c * Real.sinh (a * τ / c)) τ := by
  have h0 : HasDerivAt (fun τ : ℝ => a * τ / c) (a / c) τ := by
    simpa [mul_comm, mul_div_assoc] using
      ((hasDerivAt_id τ).const_mul a).div_const c
  have h1 : HasDerivAt (fun τ : ℝ => Real.cosh (a * τ / c))
      (Real.sinh (a * τ / c) * (a / c)) τ := h0.cosh
  have h2 := h1.const_mul (c ^ 2 / a)
  convert h2 using 1
  field_simp

