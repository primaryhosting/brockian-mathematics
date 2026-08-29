import Mathlib

/-!
# Mobius Root Sum 8
Category: Pure Mathematics
Target: Math.mobius_root_sum_8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace Math

/-- A primitive 8-th root of unity satisfies `z ^ 4 = -1`. -/
lemma pow_four_eq_neg_one {z : ℂ} (hz : IsPrimitiveRoot z 8) : z ^ 4 = -1 := by
  have h8 : z ^ 8 = 1 := hz.pow_eq_one
  have h4 : z ^ 4 ≠ 1 := hz.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
  have hfac : (z ^ 4 - 1) * (z ^ 4 + 1) = 0 := by linear_combination h8
  rcases mul_eq_zero.1 hfac with h | h
  · exact absurd (sub_eq_zero.1 h) h4
  · linear_combination h

/-- For a primitive 8-th root of unity, `z ^ 5 = -z`. -/
lemma pow_five_eq_neg {z : ℂ} (hz : IsPrimitiveRoot z 8) : z ^ 5 = -z := by
  have h := pow_four_eq_neg_one hz
  linear_combination z * h

/-- The sum of the primitive 8-th roots of unity equals `μ 8`. -/
theorem mobius_root_sum_8 :
    ∑ z ∈ primitiveRoots 8 ℂ, z = (ArithmeticFunction.moebius 8 : ℂ) := by
  have hmem : ∀ z : ℂ, z ∈ primitiveRoots 8 ℂ ↔ IsPrimitiveRoot z 8 :=
    fun z => mem_primitiveRoots (by norm_num)
  have hclosed : ∀ z ∈ primitiveRoots 8 ℂ, z ^ 5 ∈ primitiveRoots 8 ℂ := by
    intro z hz
    exact (hmem _).2 (((hmem z).1 hz).pow_of_coprime 5 (by norm_num))
  have hinv : ∀ z ∈ primitiveRoots 8 ℂ, (z ^ 5) ^ 5 = z := by
    intro z hz
    have h8 : z ^ 8 = 1 := ((hmem z).1 hz).pow_eq_one
    calc (z ^ 5) ^ 5 = (z ^ 8) ^ 3 * z := by ring
      _ = z := by rw [h8]; ring
  have key : ∑ z ∈ primitiveRoots 8 ℂ, z = ∑ z ∈ primitiveRoots 8 ℂ, z ^ 5 :=
    Finset.sum_nbij' (i := fun z => z ^ 5) (j := fun z => z ^ 5) hclosed hclosed hinv hinv
      (fun z hz => (hinv z hz).symm)
  have key2 : ∑ z ∈ primitiveRoots 8 ℂ, z ^ 5 = -∑ z ∈ primitiveRoots 8 ℂ, z := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun z hz => pow_five_eq_neg ((hmem z).1 hz)
  have hS : ∑ z ∈ primitiveRoots 8 ℂ, z = 0 := by
    have h := key.trans key2
    linear_combination h / 2
  rw [hS]
  have : ArithmeticFunction.moebius 8 = 0 := by decide
  rw [this]
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

