/-
# Mobius Root Sum 10
Category: Pure Mathematics
Target: Math.mobius_root_sum_10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Mobius Root Sum 10
Category: Pure Mathematics
Target: Math.mobius_root_sum_10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace Math

/-- The set of primitive `10`-th roots of unity in `ℂ` is `{ζ, ζ³, ζ⁷, ζ⁹}` for any
primitive `10`-th root of unity `ζ`. -/
theorem primitiveRoots_ten_eq_image {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 10) :
    primitiveRoots 10 ℂ = ({1, 3, 7, 9} : Finset ℕ).image (ζ ^ ·) := by
  ext x
  rw [mem_primitiveRoots (by norm_num), hζ.isPrimitiveRoot_iff]
  simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨i, hi, hcop, rfl⟩
    refine ⟨i, ?_, rfl⟩
    interval_cases i <;> revert hcop <;> decide
  · rintro ⟨i, hi, rfl⟩
    rcases hi with rfl | rfl | rfl | rfl <;> exact ⟨_, by norm_num, by decide, rfl⟩

/-- For a primitive `10`-th root of unity `ζ`, the sum `ζ + ζ³ + ζ⁷ + ζ⁹` equals `1`
(it is minus the coefficient of `X³` in the tenth cyclotomic polynomial
`X⁴ - X³ + X² - X + 1`). -/
theorem sum_primitive_powers_ten {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 10) :
    ζ ^ 1 + ζ ^ 3 + ζ ^ 7 + ζ ^ 9 = 1 := by
  have h10 : ζ ^ 10 = 1 := hζ.pow_eq_one
  have h5 : ζ ^ 5 ≠ 1 := hζ.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
  have h2 : ζ ^ 2 ≠ 1 := hζ.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
  have h5' : ζ ^ 5 = -1 := by
    have hfac : (ζ ^ 5 - 1) * (ζ ^ 5 + 1) = 0 := by linear_combination h10
    rcases mul_eq_zero.1 hfac with h | h
    · exact absurd (by linear_combination h) h5
    · linear_combination h
  have hne : ζ + 1 ≠ 0 := fun h => h2 (by linear_combination (ζ - 1) * h)
  have key : ζ ^ 4 - ζ ^ 3 + ζ ^ 2 - ζ + 1 = 0 := by
    have hfac : (ζ + 1) * (ζ ^ 4 - ζ ^ 3 + ζ ^ 2 - ζ + 1) = 0 := by linear_combination h5'
    exact (mul_eq_zero.1 hfac).resolve_left hne
  linear_combination (ζ ^ 2 + ζ ^ 4) * h5' - key

/-- The Möbius function at `10` equals `1`. -/
theorem moebius_ten : ArithmeticFunction.moebius 10 = 1 := by
  have h : (10 : ℕ) = 2 * 5 := by norm_num
  rw [h, ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num)]
  norm_num

/-- **Möbius root sum for `n = 10`**: the sum of the primitive `10`-th roots of unity in `ℂ`
equals `μ(10) = 1`. -/
theorem mobius_root_sum_10 :
    ∑ z ∈ primitiveRoots 10 ℂ, z = (ArithmeticFunction.moebius 10 : ℂ) := by
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ 10 :=
    ⟨Complex.exp (2 * Real.pi * Complex.I / 10), Complex.isPrimitiveRoot_exp 10 (by norm_num)⟩
  rw [primitiveRoots_ten_eq_image hζ, moebius_ten]
  rw [Finset.sum_image (by
    intro i hi j hj h
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.coe_singleton,
      Set.mem_singleton_iff] at hi hj
    exact hζ.pow_inj (by rcases hi with rfl | rfl | rfl | rfl <;> norm_num)
      (by rcases hj with rfl | rfl | rfl | rfl <;> norm_num) h)]
  have := sum_primitive_powers_ten hζ
  norm_num [Finset.sum_insert, Finset.mem_insert]
  linear_combination this

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

