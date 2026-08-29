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

theorem stride_ray_step (s k : ℕ) : ((k + 1) * s) % 5 = (k * s % 5 + s % 5) % 5 := by
  conv_lhs => rw [Nat.add_mul, one_mul, Nat.add_mod]

/-- Multiplying by `s` mod `5` only depends on `s % 5`. -/
