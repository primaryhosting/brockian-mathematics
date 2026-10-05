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
# Mobius Root Sum 12
Category: Pure Mathematics
Target: Math.mobius_root_sum_12
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Math

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

/-- If `z` is a primitive 12-th root of unity in `ℂ`, then `z ^ 6 = -1`. -/
lemma pow_six_eq_neg_one_of_isPrimitiveRoot_twelve {z : ℂ} (h : IsPrimitiveRoot z 12) :
    z ^ 6 = -1 := by
  have h12 : z ^ 12 = 1 := h.pow_eq_one
  have hne : z ^ 6 ≠ 1 := h.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
  have hsq : (z ^ 6) ^ 2 = 1 := by rw [← pow_mul]; exact h12
  have hfac : (z ^ 6 - 1) * (z ^ 6 + 1) = 0 := by linear_combination hsq
  rcases mul_eq_zero.mp hfac with h1 | h2
  · exact absurd (by linear_combination h1) hne
  · linear_combination h2

/-- Negation maps primitive 12-th roots of unity to primitive 12-th roots of unity. -/
lemma neg_mem_primitiveRoots_twelve {z : ℂ} (hz : z ∈ primitiveRoots 12 ℂ) :
    -z ∈ primitiveRoots 12 ℂ := by
  have h : IsPrimitiveRoot z 12 := (mem_primitiveRoots (by norm_num)).mp hz
  have h6 : z ^ 6 = -1 := pow_six_eq_neg_one_of_isPrimitiveRoot_twelve h
  have h7 : z ^ 7 = -z := by
    have : z ^ 7 = z ^ 6 * z := by ring
    rw [this, h6]; ring
  have hcop : Nat.Coprime 7 12 := by decide
  have := h.pow_of_coprime 7 hcop
  rw [h7] at this
  exact (mem_primitiveRoots (by norm_num)).mpr this

/-- There are exactly four primitive 12-th roots of unity in `ℂ`. -/
lemma card_primitiveRoots_twelve : (primitiveRoots 12 ℂ).card = 4 := by
  rw [Complex.card_primitiveRoots]
  decide

/-- The sum of the primitive 12-th roots of unity equals `μ 12`. -/
theorem mobius_root_sum_12 :
    ∑ z ∈ primitiveRoots 12 ℂ, z = (μ 12 : ℂ) := by
  have hmu : μ 12 = 0 :=
    moebius_eq_zero_of_not_squarefree (by decide)
  have hsum : ∑ z ∈ primitiveRoots 12 ℂ, z = ∑ z ∈ primitiveRoots 12 ℂ, (-z) := by
    refine Finset.sum_nbij' (fun z => -z) (fun z => -z) ?_ ?_ ?_ ?_ ?_
    · intro a ha; exact neg_mem_primitiveRoots_twelve ha
    · intro a ha; exact neg_mem_primitiveRoots_twelve ha
    · intro a _; ring
    · intro a _; ring
    · intro a _; ring
  rw [Finset.sum_neg_distrib] at hsum
  have h0 : ∑ z ∈ primitiveRoots 12 ℂ, z = 0 := by linear_combination hsum / 2
  rw [h0, hmu]
  norm_num

end Math

