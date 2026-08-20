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

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian
namespace ConeLine

/-- The ray reached after `k+1` strides of length `s` is obtained from the ray after `k`
strides by adding the constant `s % 5` (mod 5). -/

private lemma rayWalk_eq (s : ℕ) :
    rayWalk s = [s % 5, (2 * (s % 5)) % 5, (3 * (s % 5)) % 5, (4 * (s % 5)) % 5,
      (5 * (s % 5)) % 5] := by
  simp only [rayWalk, List.range_succ, List.range_zero]
  simp only [List.map_cons, List.map_nil, List.nil_append, List.cons_append]
  norm_num [Nat.mul_mod]

/-- Stride ray walk classification: the multiples of `s` walk the five rays in the fixed
cyclic order determined by `s % 5`.  Strides `≡ 2 (mod 5)` trace the pentagram order
`(2,4,1,3,0)`, `≡ 3` its mirror `(3,1,4,2,0)`, `≡ 1` the pentagon `(1,2,3,4,0)`,
`≡ 4` its mirror `(4,3,2,1,0)`, and `≡ 0` never leaves ray `0`. -/
