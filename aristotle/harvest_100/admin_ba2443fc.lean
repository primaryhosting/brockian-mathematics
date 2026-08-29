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

open Finset ArithmeticFunction

namespace Math

/-- If `z` is a primitive 12-th root of unity, then `z ^ 6 = -1`. -/
lemma pow_six_eq_neg_one_of_isPrimitiveRoot_twelve {z : ℂ} (h : IsPrimitiveRoot z 12) :
    z ^ 6 = -1 := by
  have h12 : (z ^ 6) ^ 2 = 1 := by
    rw [← pow_mul]
    simpa using h.pow_eq_one
  have hne : z ^ 6 ≠ 1 := h.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
  have h12' : z ^ 6 * z ^ 6 = 1 := by rw [← sq]; exact h12
  rcases mul_self_eq_one_iff.mp h12' with h1 | h1
  · exact absurd h1 hne
  · exact h1

/-- Negation maps primitive 12-th roots of unity to primitive 12-th roots of unity. -/
lemma isPrimitiveRoot_neg_twelve {z : ℂ} (h : IsPrimitiveRoot z 12) :
    IsPrimitiveRoot (-z) 12 := by
  have h6 : z ^ 6 = -1 := pow_six_eq_neg_one_of_isPrimitiveRoot_twelve h
  have hz7 : z ^ 7 = -z := by
    have : z ^ 7 = z ^ 6 * z := by ring
    rw [this, h6]; ring
  have := h.pow_of_coprime 7 (by decide)
  rwa [hz7] at this

/-- The sum of the primitive 12-th roots of unity equals `μ(12) = 0`. -/
theorem mobius_root_sum_12 :
    ∑ z ∈ primitiveRoots 12 ℂ, z = (moebius 12 : ℂ) := by
  have hmu : moebius 12 = 0 :=
    moebius_eq_zero_of_not_squarefree (n := 12) (by decide)
  have hset : (primitiveRoots 12 ℂ).image (fun z => -z) = primitiveRoots 12 ℂ := by
    apply Finset.eq_of_subset_of_card_le
    · intro w hw
      simp only [Finset.mem_image] at hw
      obtain ⟨z, hz, rfl⟩ := hw
      rw [mem_primitiveRoots (by norm_num)] at hz ⊢
      exact isPrimitiveRoot_neg_twelve hz
    · exact le_of_eq (Finset.card_image_of_injective _ neg_injective).symm
  have key : ∑ z ∈ primitiveRoots 12 ℂ, z = -∑ z ∈ primitiveRoots 12 ℂ, z := by
    conv_lhs => rw [← hset]
    rw [Finset.sum_image (fun a _ b _ h => neg_injective h), ← Finset.sum_neg_distrib]
  have : (2 : ℂ) * ∑ z ∈ primitiveRoots 12 ℂ, z = 0 := by
    linear_combination key
  have hsum : ∑ z ∈ primitiveRoots 12 ℂ, z = 0 := by
    have h2 : (2 : ℂ) ≠ 0 := by norm_num
    exact (mul_eq_zero.mp this).resolve_left h2
  rw [hsum, hmu]
  simp

end Math

