import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-
# Mobius Root Sum 9
Category: Pure Mathematics
Target: Math.mobius_root_sum_9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Finset

namespace Math

/-- A fixed primitive 9-th root of unity in `ℂ`. -/

theorem zeta9_cube_sum : 1 + zeta9 ^ 3 + zeta9 ^ 6 = 0 := by
  have h9 : zeta9 ^ 9 = 1 := isPrimitiveRoot_zeta9.pow_eq_one
  have hne : zeta9 ^ 3 - 1 ≠ 0 := fun h =>
    isPrimitiveRoot_zeta9.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num) (sub_eq_zero.mp h)
  have key : (zeta9 ^ 3 - 1) * (1 + zeta9 ^ 3 + zeta9 ^ 6) = 0 := by
    linear_combination h9
  rcases mul_eq_zero.mp key with h | h
  · exact absurd h hne
  · exact h

/-- **The sum of the primitive 9-th roots of unity equals `μ(9)`.** -/
