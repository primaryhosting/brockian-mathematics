import Mathlib

/-!
# Mobius Root Sum 12
Category: Pure Mathematics
Target: Math.mobius_root_sum_12
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

/-- If `z` is a primitive `12`-th root of unity in a domain, then `z ^ 6 = -1`. -/

theorem isPrimitiveRoot_neg_of_twelve {R : Type*} [CommRing R] [IsDomain R]
    {z : R} (hz : IsPrimitiveRoot z 12) : IsPrimitiveRoot (-z) 12 := by
  have h6 : z ^ 6 = -1 := pow_six_eq_neg_one_of_isPrimitiveRoot_twelve hz
  have hz7 : -z = z ^ 7 := by
    have h7 : z ^ 7 = z ^ 6 * z := by ring
    rw [h7, h6]; ring
  rw [hz7]
  exact hz.pow_of_coprime 7 (by decide)

/-- The sum of the primitive `12`-th roots of unity in `ℂ` equals `μ(12) = 0`. -/
