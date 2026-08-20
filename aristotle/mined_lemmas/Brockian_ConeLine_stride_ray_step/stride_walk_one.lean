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

theorem stride_walk_one (s : ℕ) (h : s % 5 = 1) :
    (List.range 5).map (fun k => ((k + 1) * s) % 5) = [1, 2, 3, 4, 0] := by
  simp [List.range_succ, Nat.mul_mod, h]

/-- Stride ≡ 4 (mod 5): the mirrored pentagon order. -/
