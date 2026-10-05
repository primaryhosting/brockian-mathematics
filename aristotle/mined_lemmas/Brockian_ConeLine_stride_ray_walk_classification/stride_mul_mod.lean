/-
# Stride Ray Walk Classification
Category: Cone Line
Target: Brockian.ConeLine.stride_ray_walk_classification
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Brockian.ConeLine

/-- The ray reached after `k+1` strides only depends on the previous ray and `s % 5`. -/

theorem stride_mul_mod (n s : ℕ) : (n * s) % 5 = (n * (s % 5)) % 5 := by
  simp [Nat.mul_mod]

