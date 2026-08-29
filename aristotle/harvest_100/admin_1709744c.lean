/-
# Mobius Root Sum 3
Category: Pure Mathematics
Target: Math.mobius_root_sum_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Finset Complex

namespace Math

/-- The sum of the primitive `3`-rd roots of unity in `ℂ` equals `μ(3) = -1`. -/
theorem mobius_root_sum_3 :
    ∑ z ∈ primitiveRoots 3 ℂ, z = ((ArithmeticFunction.moebius 3 : ℤ) : ℂ) := by
  set ζ : ℂ := Complex.exp (2 * Real.pi * I / 3) with hζdef
  have hζ : IsPrimitiveRoot ζ 3 := Complex.isPrimitiveRoot_exp 3 (by norm_num)
  have hne : ζ ≠ ζ ^ 2 := by
    intro h
    have := hζ.pow_inj (i := 1) (j := 2) (by norm_num) (by norm_num) (by simpa using h)
    omega
  have hsub : ({ζ, ζ ^ 2} : Finset ℂ) ⊆ primitiveRoots 3 ℂ := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact (mem_primitiveRoots (by norm_num)).2 hζ
    · exact (mem_primitiveRoots (by norm_num)).2 (hζ.pow_of_coprime 2 (by decide))
  have hcard : (primitiveRoots 3 ℂ).card = 2 := by
    rw [Complex.card_primitiveRoots]; decide
  have heq : primitiveRoots 3 ℂ = {ζ, ζ ^ 2} := by
    refine (Finset.eq_of_subset_of_card_le hsub ?_).symm
    rw [hcard, Finset.card_insert_of_notMem (by simpa using hne), Finset.card_singleton]
  rw [heq, Finset.sum_insert (by simpa using hne), Finset.sum_singleton]
  have h0 : ∑ i ∈ Finset.range 3, ζ ^ i = 0 := hζ.geom_sum_eq_zero (by norm_num)
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one] at h0
  rw [ArithmeticFunction.moebius_apply_prime (by norm_num)]
  push_cast
  linear_combination h0

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

