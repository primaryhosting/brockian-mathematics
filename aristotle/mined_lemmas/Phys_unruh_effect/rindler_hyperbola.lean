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

theorem rindler_hyperbola (a c τ : ℝ) :
    (rindlerX a c τ) ^ 2 - c ^ 2 * (rindlerT a c τ) ^ 2 = (c ^ 2 / a) ^ 2 := by
  have h := Real.cosh_sq_sub_sinh_sq (a * τ / c)
  unfold rindlerX rindlerT
  linear_combination ((c ^ 2 / a) ^ 2) * h

