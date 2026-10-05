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

theorem mobius_root_sum_12 :
    ∑ z ∈ primitiveRoots 12 ℂ, z = (ArithmeticFunction.moebius 12 : ℂ) := by
  have hmu : ArithmeticFunction.moebius 12 = 0 :=
    ArithmeticFunction.moebius_eq_zero_of_not_squarefree (by decide)
  rw [hmu]
  push_cast
  refine Finset.sum_involution (fun z _ => -z) ?_ ?_ ?_ ?_
  · intro z _
    ring
  · intro z _ hz0 h
    apply hz0
    linear_combination (-1/2 : ℂ) * h
  · intro z hz
    rw [mem_primitiveRoots (by norm_num)] at hz ⊢
    exact isPrimitiveRoot_neg_of_twelve hz
  · intro z _
    ring

end Math

