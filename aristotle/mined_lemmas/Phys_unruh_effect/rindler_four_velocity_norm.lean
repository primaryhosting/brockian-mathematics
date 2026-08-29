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

theorem rindler_four_velocity_norm (a c τ : ℝ) (ha : a ≠ 0) (hc : c ≠ 0) :
    c ^ 2 * (deriv (rindlerT a c) τ) ^ 2 - (deriv (rindlerX a c) τ) ^ 2 = c ^ 2 := by
  rw [(hasDerivAt_rindlerT a c τ ha hc).deriv, (hasDerivAt_rindlerX a c τ ha hc).deriv]
  have h := Real.cosh_sq_sub_sinh_sq (a * τ / c)
  nlinarith [h]

/-- The worldline has constant proper acceleration `a`: the four-acceleration is a
spacelike vector of norm `a`, `(d²x/dτ²)² - c² (d²t/dτ²)² = a²`. -/
