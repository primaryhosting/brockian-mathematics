import Mathlib

/-!
# Mobius Root Sum 8
Category: Pure Mathematics
Target: Math.mobius_root_sum_8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

open ArithmeticFunction

/-- A primitive `8`-th root of unity satisfies `z ^ 4 = -1`. -/
lemma pow_four_eq_neg_one_of_isPrimitiveRoot_eight {z : ℂ} (hz : IsPrimitiveRoot z 8) :
    z ^ 4 = -1 := by
  have h8 : z ^ 8 = 1 := hz.pow_eq_one
  have hsq : z ^ 4 * z ^ 4 = 1 := by
    rw [← pow_add]; simpa using h8
  have h4 : z ^ 4 ≠ 1 := hz.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
  rcases mul_self_eq_one_iff.mp hsq with h | h
  · exact absurd h h4
  · exact h

/-- Negation maps primitive `8`-th roots of unity to primitive `8`-th roots of unity. -/
lemma isPrimitiveRoot_neg_of_isPrimitiveRoot_eight {z : ℂ} (hz : IsPrimitiveRoot z 8) :
    IsPrimitiveRoot (-z) 8 := by
  have h4 : z ^ 4 = -1 := pow_four_eq_neg_one_of_isPrimitiveRoot_eight hz
  have hneg : -z = z ^ 5 := by
    have h5 : z ^ 5 = z ^ 4 * z := by ring
    rw [h5, h4]; ring
  rw [hneg]
  exact hz.pow_of_coprime 5 (by norm_num)

/-- The sum of the primitive `8`-th roots of unity in `ℂ` equals `μ 8`. -/
theorem mobius_root_sum_8 :
    ∑ z ∈ primitiveRoots 8 ℂ, z = (moebius 8 : ℤ) := by
  have hmem : ∀ z : ℂ, z ∈ primitiveRoots 8 ℂ ↔ IsPrimitiveRoot z 8 := fun z =>
    mem_primitiveRoots (by norm_num)
  have hmap : ∀ z ∈ primitiveRoots 8 ℂ, -z ∈ primitiveRoots 8 ℂ := by
    intro z hz
    exact (hmem _).2 (isPrimitiveRoot_neg_of_isPrimitiveRoot_eight ((hmem z).1 hz))
  have key : ∑ z ∈ primitiveRoots 8 ℂ, z = ∑ z ∈ primitiveRoots 8 ℂ, (-z) := by
    refine Finset.sum_nbij' (fun z => -z) (fun z => -z) hmap hmap ?_ ?_ ?_ <;> intros <;> simp
  have hzero : ∑ z ∈ primitiveRoots 8 ℂ, z = 0 := by
    rw [Finset.sum_neg_distrib] at key
    linear_combination key / 2
  rw [hzero]
  rw [moebius_eq_zero_of_not_squarefree (n := 8) (by decide)]
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

