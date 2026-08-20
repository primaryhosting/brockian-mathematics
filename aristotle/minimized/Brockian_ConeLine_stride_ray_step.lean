import Mathlib

/-!
# Stride Ray Walk Classification
Category: Cone Line
Target: Brockian.ConeLine.stride_ray_walk_classification
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 800000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian.ConeLine

/-- Each successive multiple of the stride `s` advances the ray index by the
constant step `s % 5`. -/

theorem stride_ray_step (s k : ℕ) : ((k + 1) * s) % 5 = (k * s % 5 + s % 5) % 5 := by
  rw [Nat.add_mul, one_mul, Nat.add_mod]

/-- Stride ≡ 2 (mod 5): the walk traces the pentagram order. -/
