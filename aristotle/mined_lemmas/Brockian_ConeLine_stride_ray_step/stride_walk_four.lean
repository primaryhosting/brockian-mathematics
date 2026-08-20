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

theorem stride_walk_four (s : ℕ) (h : s % 5 = 4) :
    (List.range 5).map (fun k => ((k + 1) * s) % 5) = [4, 3, 2, 1, 0] := by
  simp [List.range_succ, Nat.mul_mod, h]

/-- Stride ≡ 0 (mod 5): the walk never leaves ray 0. -/
