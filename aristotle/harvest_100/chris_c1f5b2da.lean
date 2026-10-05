/-
# Mobius Root Sum 11
Category: Pure Mathematics
Target: Math.mobius_root_sum_11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Mobius Root Sum 11

The sum of the primitive 11-th roots of unity in `ℂ` equals `μ(11)`.
-/

open Finset Polynomial

namespace Math

/-- The 11-th roots of unity in `ℂ` are exactly the powers `ζ ^ i`, `i < 11`, of a primitive
11-th root of unity `ζ`. -/
lemma nthRootsFinset_eq_image_pow {ζ : ℂ} (h : IsPrimitiveRoot ζ 11) :
    nthRootsFinset 11 (1 : ℂ) = (Finset.range 11).image (fun i => ζ ^ i) := by
  have hsub : (Finset.range 11).image (fun i => ζ ^ i) ⊆ nthRootsFinset 11 (1 : ℂ) := by
    intro x hx
    simp only [Finset.mem_image, Finset.mem_range] at hx
    obtain ⟨i, _, rfl⟩ := hx
    exact (Polynomial.mem_nthRootsFinset (by norm_num) 1).2 (by
      rw [← pow_mul, mul_comm, pow_mul, h.pow_eq_one, one_pow])
  have hcard : #((Finset.range 11).image (fun i => ζ ^ i)) = 11 := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj hij
    exact h.pow_inj (Finset.mem_range.1 hi) (Finset.mem_range.1 hj) hij
  exact (Finset.eq_of_subset_of_card_le hsub (by rw [hcard, h.card_nthRootsFinset])).symm

/-- The sum of all 11-th roots of unity in `ℂ` vanishes. -/
lemma sum_nthRootsFinset_eq_zero : ∑ z ∈ nthRootsFinset 11 (1 : ℂ), z = 0 := by
  obtain ⟨ζ, h⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ 11 :=
    ⟨_, Complex.isPrimitiveRoot_exp 11 (by norm_num)⟩
  rw [nthRootsFinset_eq_image_pow h, Finset.sum_image]
  · exact h.geom_sum_eq_zero (by norm_num)
  · intro i hi j hj hij
    exact h.pow_inj (Finset.mem_range.1 hi) (Finset.mem_range.1 hj) hij

/-- The 11-th roots of unity are `1` together with the primitive ones. -/
lemma nthRootsFinset_eq_insert_one :
    nthRootsFinset 11 (1 : ℂ) = insert 1 (primitiveRoots 11 ℂ) := by
  classical
  rw [IsPrimitiveRoot.nthRoots_one_eq_biUnion_primitiveRoots]
  have hdiv : Nat.divisors 11 = {1, 11} := by decide
  rw [hdiv]
  simp [Finset.biUnion_insert, IsPrimitiveRoot.primitiveRoots_one]

/-- `1` is not a primitive 11-th root of unity. -/
lemma one_notMem_primitiveRoots : (1 : ℂ) ∉ primitiveRoots 11 ℂ := by
  intro hmem
  have := isPrimitiveRoot_of_mem_primitiveRoots hmem
  have := this.unique (IsPrimitiveRoot.one_right_iff.2 rfl)
  omega

/-- **Mobius root sum 11**: the sum of the primitive 11-th roots of unity in `ℂ` equals
`μ(11) = -1`. -/
theorem mobius_root_sum_11 :
    ∑ z ∈ primitiveRoots 11 ℂ, z = (ArithmeticFunction.moebius 11 : ℂ) := by
  have hmu : (ArithmeticFunction.moebius 11 : ℤ) = -1 :=
    ArithmeticFunction.moebius_apply_prime (by norm_num)
  have hsum := sum_nthRootsFinset_eq_zero
  rw [nthRootsFinset_eq_insert_one, Finset.sum_insert one_notMem_primitiveRoots] at hsum
  have : ∑ z ∈ primitiveRoots 11 ℂ, z = -1 := by linear_combination hsum
  rw [this, hmu]
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

