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

/-- A fixed primitive `8`-th root of unity in `ℂ`. -/
noncomputable def zeta8 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 8)

theorem isPrimitiveRoot_zeta8 : IsPrimitiveRoot zeta8 8 := by
  simpa [zeta8] using Complex.isPrimitiveRoot_exp 8 (by norm_num)

theorem zeta8_pow_ne (i j : ℕ) (hi : i < 8) (hj : j < 8) (hij : i ≠ j) :
    zeta8 ^ i ≠ zeta8 ^ j :=
  fun h => hij (isPrimitiveRoot_zeta8.pow_inj hi hj h)

/-- The primitive `8`-th roots of unity are exactly `ζ, ζ³, ζ⁵, ζ⁷`. -/
theorem primitiveRoots_eight :
    primitiveRoots 8 ℂ = {zeta8, zeta8 ^ 3, zeta8 ^ 5, zeta8 ^ 7} := by
  have hsub : ({zeta8, zeta8 ^ 3, zeta8 ^ 5, zeta8 ^ 7} : Finset ℂ) ⊆ primitiveRoots 8 ℂ := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [mem_primitiveRoots (by norm_num)]
    rcases hx with h | h | h | h <;> subst h
    · exact isPrimitiveRoot_zeta8
    · exact isPrimitiveRoot_zeta8.pow_of_coprime 3 (by decide)
    · exact isPrimitiveRoot_zeta8.pow_of_coprime 5 (by decide)
    · exact isPrimitiveRoot_zeta8.pow_of_coprime 7 (by decide)
  have h1 := zeta8_pow_ne 1 3 (by norm_num) (by norm_num) (by norm_num)
  have h2 := zeta8_pow_ne 1 5 (by norm_num) (by norm_num) (by norm_num)
  have h3 := zeta8_pow_ne 1 7 (by norm_num) (by norm_num) (by norm_num)
  have h4 := zeta8_pow_ne 3 5 (by norm_num) (by norm_num) (by norm_num)
  have h5 := zeta8_pow_ne 3 7 (by norm_num) (by norm_num) (by norm_num)
  have h6 := zeta8_pow_ne 5 7 (by norm_num) (by norm_num) (by norm_num)
  simp only [pow_one] at h1 h2 h3
  have hcard : #({zeta8, zeta8 ^ 3, zeta8 ^ 5, zeta8 ^ 7} : Finset ℂ) = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [h1, h2, h3]),
      Finset.card_insert_of_notMem (by simp [h4, h5]),
      Finset.card_insert_of_notMem (by simp [h6]), Finset.card_singleton]
  refine (Finset.eq_of_subset_of_card_le hsub ?_).symm
  rw [hcard, Complex.card_primitiveRoots]
  decide

theorem zeta8_pow_four : zeta8 ^ 4 = -1 := by
  have h8 : (zeta8 ^ 4) ^ 2 = 1 := by
    rw [← pow_mul]; exact isPrimitiveRoot_zeta8.pow_eq_one
  have h : (zeta8 ^ 4 - 1) * (zeta8 ^ 4 + 1) = 0 := by linear_combination h8
  rcases mul_eq_zero.mp h with h' | h'
  · exact absurd (by linear_combination h' : zeta8 ^ 4 = 1)
      (isPrimitiveRoot_zeta8.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num))
  · linear_combination h'

/-- The sum of the primitive `8`-th roots of unity in `ℂ` equals `μ(8) = 0`. -/
theorem mobius_root_sum_8 :
    ∑ x ∈ primitiveRoots 8 ℂ, x = (ArithmeticFunction.moebius 8 : ℂ) := by
  have h1 := zeta8_pow_ne 1 3 (by norm_num) (by norm_num) (by norm_num)
  have h2 := zeta8_pow_ne 1 5 (by norm_num) (by norm_num) (by norm_num)
  have h3 := zeta8_pow_ne 1 7 (by norm_num) (by norm_num) (by norm_num)
  have h4 := zeta8_pow_ne 3 5 (by norm_num) (by norm_num) (by norm_num)
  have h5 := zeta8_pow_ne 3 7 (by norm_num) (by norm_num) (by norm_num)
  have h6 := zeta8_pow_ne 5 7 (by norm_num) (by norm_num) (by norm_num)
  simp only [pow_one] at h1 h2 h3
  have hmu : (ArithmeticFunction.moebius 8 : ℤ) = 0 := by decide
  rw [primitiveRoots_eight, Finset.sum_insert (by simp [h1, h2, h3]),
    Finset.sum_insert (by simp [h4, h5]), Finset.sum_insert (by simp [h6]),
    Finset.sum_singleton, hmu]
  push_cast
  linear_combination (zeta8 + zeta8 ^ 3) * zeta8_pow_four

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

