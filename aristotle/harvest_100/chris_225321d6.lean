/-
# Mobius Root Sum 8
Category: Pure Mathematics
Target: Math.mobius_root_sum_8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators

namespace Math

/-- A primitive `8`-th root of unity satisfies `ζ ^ 4 = -1`. -/
lemma pow_four_eq_neg_one_of_isPrimitiveRoot_eight {z : ℂ} (hz : IsPrimitiveRoot z 8) :
    z ^ 4 = -1 := by
  have h8 : (z ^ 4) ^ 2 = 1 := by
    rw [← pow_mul]; simpa using hz.pow_eq_one
  have h4 : z ^ 4 ≠ 1 := hz.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
  have h8' : z ^ 4 * z ^ 4 = 1 := by rw [← sq]; exact h8
  rcases mul_self_eq_one_iff.1 h8' with h | h
  · exact absurd h h4
  · exact h

/-- Negation maps primitive `8`-th roots of unity to primitive `8`-th roots of unity. -/
lemma neg_mem_primitiveRoots_eight {z : ℂ} (hz : z ∈ primitiveRoots 8 ℂ) :
    -z ∈ primitiveRoots 8 ℂ := by
  rw [mem_primitiveRoots (by norm_num)] at hz ⊢
  have h5 : IsPrimitiveRoot (z ^ 5) 8 := hz.pow_of_coprime 5 (by norm_num [Nat.Coprime])
  have : z ^ 5 = -z := by
    have h4 := pow_four_eq_neg_one_of_isPrimitiveRoot_eight hz
    calc z ^ 5 = z ^ 4 * z := by ring
    _ = -z := by rw [h4]; ring
  rwa [this] at h5

/-- The sum of the primitive `8`-th roots of unity in `ℂ` equals `μ 8` (which is `0`).

The primitive `8`-th roots of unity are closed under negation and none of them is zero,
so they pair off and the sum vanishes; and `μ 8 = 0` since `8 = 2 ^ 3` is not squarefree. -/
theorem mobius_root_sum_8 :
    ∑ z ∈ primitiveRoots 8 ℂ, z = (ArithmeticFunction.moebius 8 : ℂ) := by
  have hmu : (ArithmeticFunction.moebius 8 : ℤ) = 0 := by decide
  rw [hmu]
  push_cast
  refine Finset.sum_involution (fun z _ => -z) (fun a _ => by ring) ?_
    (fun a ha => neg_mem_primitiveRoots_eight ha) (fun a _ => neg_neg a)
  intro a _ ha0 h
  exact ha0 (by linear_combination -h / 2)

end Math

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

