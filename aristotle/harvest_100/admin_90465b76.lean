/-
# Mobius Root Sum 8
Category: Pure Mathematics
Target: Math.mobius_root_sum_8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Finset

namespace Math

/-- A primitive `8`-th root of unity satisfies `z ^ 4 = -1`. -/
theorem primRoot8_pow_four {z : ℂ} (h : IsPrimitiveRoot z 8) : z ^ 4 = -1 := by
  have h8 : z ^ 8 = 1 := h.pow_eq_one
  have h4 : z ^ 4 ≠ 1 := h.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
  have hfac : (z ^ 4 - 1) * (z ^ 4 + 1) = 0 := by linear_combination h8
  rcases mul_eq_zero.1 hfac with h1 | h1
  · exact absurd (by linear_combination h1) h4
  · linear_combination h1

/-- The negation of a primitive `8`-th root of unity is again one (indeed `-z = z ^ 5`). -/
theorem isPrimitiveRoot_neg_of_eight {z : ℂ} (h : IsPrimitiveRoot z 8) :
    IsPrimitiveRoot (-z) 8 := by
  have h5 : z ^ 5 = -z := by
    have h4 := primRoot8_pow_four h
    calc z ^ 5 = z ^ 4 * z := by ring
      _ = -z := by rw [h4]; ring
  have := h.pow_of_coprime 5 (by decide)
  rwa [h5] at this

/-- **Möbius root sum for `n = 8`.** The sum of the primitive `8`-th roots of unity in `ℂ`
equals `μ 8` (which is `0`, since `8` is not squarefree).

The proof uses the fixed-point-free involution `z ↦ -z` on the set of primitive `8`-th roots
of unity, which forces the sum to be its own negative. -/
theorem mobius_root_sum_8 :
    ∑ z ∈ primitiveRoots 8 ℂ, z = (ArithmeticFunction.moebius 8 : ℂ) := by
  have hset : (primitiveRoots 8 ℂ).image (fun z => -z) = primitiveRoots 8 ℂ := by
    ext z
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact (mem_primitiveRoots (by norm_num)).2
        (isPrimitiveRoot_neg_of_eight ((mem_primitiveRoots (by norm_num)).1 hw))
    · intro hz
      refine ⟨-z, (mem_primitiveRoots (by norm_num)).2
        (isPrimitiveRoot_neg_of_eight ((mem_primitiveRoots (by norm_num)).1 hz)), by ring⟩
  have hsum : ∑ z ∈ primitiveRoots 8 ℂ, z = -∑ z ∈ primitiveRoots 8 ℂ, z := by
    conv_lhs => rw [← hset]
    rw [Finset.sum_image (by intro a _ b _ hab; simpa using hab), ← Finset.sum_neg_distrib]
  have h0 : ∑ z ∈ primitiveRoots 8 ℂ, z = 0 := by linear_combination hsum / 2
  rw [h0, ArithmeticFunction.moebius_eq_zero_of_not_squarefree (by decide : ¬ Squarefree 8)]
  norm_num

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

