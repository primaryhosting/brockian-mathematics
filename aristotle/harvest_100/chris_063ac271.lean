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
lemma pow_six_eq_neg_one_of_isPrimitiveRoot {ζ : ℂ} (h : IsPrimitiveRoot ζ 12) :
    ζ ^ 6 = -1 := by
  have h12 : (ζ ^ 6) * (ζ ^ 6) = 1 := by
    rw [← pow_add]
    exact h.pow_eq_one
  rcases mul_self_eq_one_iff.1 h12 with h1 | h1
  · exact absurd ((h.pow_eq_one_iff_dvd 6).1 h1) (by decide)
  · exact h1

/-- The negative of a primitive 12-th root of unity is again a primitive 12-th root of
unity, since `-ζ = ζ ^ 7` and `7` is coprime to `12`. -/
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
theorem mobius_root_sum_12 :
    ∑ ζ ∈ primitiveRoots 12 ℂ, ζ = ((ArithmeticFunction.moebius 12 : ℤ) : ℂ) := by
  have hmu : ArithmeticFunction.moebius 12 = 0 :=
    ArithmeticFunction.moebius_eq_zero_of_not_squarefree (by decide)
  rw [hmu]
  push_cast
  refine Finset.sum_involution (fun ζ _ => -ζ) ?_ ?_ ?_ ?_
  · intro a _
    ring
  · intro a _ ha hcon
    exact ha (by linear_combination (-1/2 : ℂ) * hcon)
  · intro a ha
    rw [mem_primitiveRoots (by norm_num)] at ha ⊢
    exact isPrimitiveRoot_neg_of_isPrimitiveRoot ha
  · intro a _
    ring

end Math

