/-
# Mobius Root Sum 10
Category: Pure Mathematics
Target: Math.mobius_root_sum_10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Mobius Root Sum 10
Category: Pure Mathematics
Target: Math.mobius_root_sum_10
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

namespace Math

/-- A fixed primitive 10-th root of unity in `ℂ`. -/

theorem zeta10_geom : 1 + zeta10 ^ 2 + zeta10 ^ 4 + zeta10 ^ 6 + zeta10 ^ 8 = 0 := by
  have hz := isPrimitiveRoot_zeta10
  have h10 : zeta10 ^ 10 = 1 := hz.pow_eq_one
  have h2 : zeta10 ^ 2 ≠ 1 := hz.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
  have hne : zeta10 ^ 2 - 1 ≠ 0 := sub_ne_zero.mpr h2
  have hmul : (zeta10 ^ 2 - 1) * (1 + zeta10 ^ 2 + zeta10 ^ 4 + zeta10 ^ 6 + zeta10 ^ 8) = 0 := by
    linear_combination h10
  exact (mul_eq_zero.mp hmul).resolve_left hne

/-- The sum of the primitive 10-th roots of unity equals `μ(10) = 1`. -/
