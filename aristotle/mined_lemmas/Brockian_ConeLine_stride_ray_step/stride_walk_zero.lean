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

theorem stride_walk_zero (s : ℕ) (h : s % 5 = 0) :
    (List.range 5).map (fun k => ((k + 1) * s) % 5) = [0, 0, 0, 0, 0] := by
  simp [List.range_succ, Nat.mul_mod, h]

/-- **Stride ray walk classification.** The multiples of a stride `s` walk the five rays
with the constant step `s % 5`, and the resulting cyclic order is determined entirely by
the residue `s % 5`: `2` gives the pentagram `(2,4,1,3,0)`, `3` its mirror `(3,1,4,2,0)`,
`1` the pentagon `(1,2,3,4,0)`, `4` its mirror `(4,3,2,1,0)`, and `0` stays on ray `0`. -/
