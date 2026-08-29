/-
# Mobius Root Sum 11
Category: Pure Mathematics
Target: Math.mobius_root_sum_11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Finset Polynomial

namespace Math

/-- The 11-th roots of unity in `ℂ` are exactly the powers `ζ ^ i`, `i < 11`, of a primitive
one. -/
lemma nthRootsFinset_eq_image_pow {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 11) :
    nthRootsFinset 11 (1 : ℂ) = (Finset.range 11).image (fun i => ζ ^ i) := by
  refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
  · intro x hx
    simp only [Finset.mem_image, Finset.mem_range] at hx
    obtain ⟨i, _, rfl⟩ := hx
    rw [Polynomial.mem_nthRootsFinset (by norm_num)]
    rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  · rw [hζ.card_nthRootsFinset]
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj hij
    simp only [Finset.mem_coe, Finset.mem_range] at hi hj
    exact hζ.pow_inj hi hj hij

/-- The sum of all 11-th roots of unity in `ℂ` is `0`. -/
lemma sum_nthRootsFinset_eq_zero : ∑ x ∈ nthRootsFinset 11 (1 : ℂ), x = 0 := by
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ 11 :=
    ⟨Complex.exp (2 * Real.pi * Complex.I / 11), Complex.isPrimitiveRoot_exp 11 (by norm_num)⟩
  rw [nthRootsFinset_eq_image_pow hζ,
    Finset.sum_image (fun i hi j hj hij => hζ.pow_inj (Finset.mem_range.1 hi)
      (Finset.mem_range.1 hj) hij)]
  exact hζ.geom_sum_eq_zero (by norm_num)

/-- The 11-th roots of unity split as `{1}` together with the primitive ones. -/
lemma nthRootsFinset_eq_insert_primitiveRoots :
    nthRootsFinset 11 (1 : ℂ) = insert 1 (primitiveRoots 11 ℂ) := by
  classical
  rw [IsPrimitiveRoot.nthRoots_one_eq_biUnion_primitiveRoots]
  have hdiv : Nat.divisors 11 = {1, 11} := by decide
  rw [hdiv]
  simp [Finset.biUnion_insert, IsPrimitiveRoot.primitiveRoots_one]

/-- **Mobius Root Sum 11**: the sum of the primitive 11-th roots of unity equals `μ 11`. -/
theorem mobius_root_sum_11 :
    ∑ ζ ∈ primitiveRoots 11 ℂ, ζ = (ArithmeticFunction.moebius 11 : ℂ) := by
  classical
  have h1 : (1 : ℂ) ∉ primitiveRoots 11 ℂ := by
    intro h
    have := (isPrimitiveRoot_of_mem_primitiveRoots h).pow_eq_one_iff_dvd 1
    simp at this
  have hsum := sum_nthRootsFinset_eq_zero
  rw [nthRootsFinset_eq_insert_primitiveRoots, Finset.sum_insert h1] at hsum
  have hmu : ArithmeticFunction.moebius 11 = -1 :=
    ArithmeticFunction.moebius_apply_prime (by norm_num)
  rw [hmu]
  push_cast
  linear_combination hsum

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

