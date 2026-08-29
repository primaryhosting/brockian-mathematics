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

theorem rindler_euclidean_periodic (a c : ℝ) (ha : a ≠ 0) (hc : c ≠ 0) (τ : ℝ) :
    rindlerXE a c (τ + 2 * Real.pi * c / a) = rindlerXE a c τ ∧
    rindlerTE a c (τ + 2 * Real.pi * c / a) = rindlerTE a c τ := by
  have harg : a * (τ + 2 * Real.pi * c / a) / c = a * τ / c + 2 * Real.pi := by
    field_simp
  constructor
  · simp [rindlerXE, harg, Real.cos_add_two_pi]
  · simp [rindlerTE, harg, Real.sin_add_two_pi]

/-- The Euclidean period `β = 2 π c / a` is exactly the inverse temperature
`ℏ / (k_B T)` for the Unruh temperature `T`. -/
