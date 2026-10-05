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

import Mathlib

/-!
# Mobius Root Sum 12
Category: Pure Mathematics
Target: Math.mobius_root_sum_12
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace Math

/-- If `ζ` is a primitive 12-th root of unity in `ℂ`, then `ζ ^ 6 = -1`. -/

lemma isPrimitiveRoot_neg_of_isPrimitiveRoot {ζ : ℂ} (h : IsPrimitiveRoot ζ 12) :
    IsPrimitiveRoot (-ζ) 12 := by
  have h7 : ζ ^ 7 = -ζ := by
    have h6 : ζ ^ 7 = ζ ^ 6 * ζ := by ring
    rw [h6, pow_six_eq_neg_one_of_isPrimitiveRoot h, neg_one_mul]
  rw [← h7]
  exact h.pow_of_coprime 7 (by decide)

/-- **Mobius Root Sum 12.**  The sum of the primitive 12-th roots of unity in `ℂ`
equals `μ(12)` (which is `0`, since `12 = 2 ^ 2 * 3` is not squarefree).

The proof pairs each primitive root `ζ` with `-ζ`, which is again primitive; this
fixed-point-free involution makes the sum vanish. -/
