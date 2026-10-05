/-
# Mobius Root Sum 10
Category: Pure Mathematics
Target: Math.mobius_root_sum_10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Polynomial

namespace Math

/-- The tenth cyclotomic polynomial over `ℂ` is `X^4 - X^3 + X^2 - X + 1`. -/
theorem cyclotomic_ten_complex :
    cyclotomic 10 ℂ = X ^ 4 - X ^ 3 + X ^ 2 - X + 1 := by
  have h := prod_cyclotomic_eq_X_pow_sub_one (n := 10) (by norm_num) ℂ
  have hd : (10 : ℕ).divisors = {1, 2, 5, 10} := by decide
  rw [hd] at h
  have h5 : cyclotomic 5 ℂ = X ^ 4 + X ^ 3 + X ^ 2 + X + 1 := by
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    rw [cyclotomic_prime]
    simp [Finset.sum_range_succ]
    ring
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_singleton, cyclotomic_one, cyclotomic_two, h5] at h
  have hne1 : ((X : ℂ[X]) - 1) ≠ 0 := by
    intro h0
    have := congrArg (fun p => Polynomial.coeff p 1) h0
    simp [Polynomial.coeff_one] at this
  have hne2 : ((X : ℂ[X]) + 1) ≠ 0 := by
    intro h0
    have := congrArg (fun p => Polynomial.coeff p 1) h0
    simp [Polynomial.coeff_one] at this
  have hne5 : ((X : ℂ[X]) ^ 4 + X ^ 3 + X ^ 2 + X + 1) ≠ 0 := by
    intro h0
    have := congrArg (fun p => Polynomial.coeff p 0) h0
    simp at this
  have key : ((X : ℂ[X]) - 1) * ((X + 1) * ((X ^ 4 + X ^ 3 + X ^ 2 + X + 1) * cyclotomic 10 ℂ))
      = (X - 1) * ((X + 1) *
          ((X ^ 4 + X ^ 3 + X ^ 2 + X + 1) * (X ^ 4 - X ^ 3 + X ^ 2 - X + 1))) := by
    rw [h]; ring
  exact mul_left_cancel₀ hne5 (mul_left_cancel₀ hne2 (mul_left_cancel₀ hne1 key))

/-- The Möbius function at `10` equals `1`. -/
theorem moebius_ten : ArithmeticFunction.moebius 10 = 1 := by
  have hmul :=
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
      (m := 2) (n := 5) (by norm_num)
  rw [show (10 : ℕ) = 2 * 5 by norm_num, hmul,
    ArithmeticFunction.moebius_apply_prime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num)]
  norm_num

/-- **Sum of the primitive 10-th roots of unity.**
The sum of the primitive 10-th roots of unity in `ℂ` equals `μ(10) = 1`. -/
theorem mobius_root_sum_10 :
    ∑ z ∈ primitiveRoots 10 ℂ, z = (ArithmeticFunction.moebius 10 : ℂ) := by
  have hz : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / 10)) 10 :=
    Complex.isPrimitiveRoot_exp 10 (by norm_num)
  have hprod := cyclotomic_eq_prod_X_sub_primitiveRoots hz
  have hdeg : (cyclotomic 10 ℂ).natDegree = 4 := by
    rw [natDegree_cyclotomic]; decide
  have h1 : (cyclotomic 10 ℂ).nextCoeff = -1 := by
    rw [nextCoeff_of_natDegree_pos (by rw [hdeg]; norm_num), hdeg, cyclotomic_ten_complex]
    simp [coeff_one, coeff_X]
  have h2 : (cyclotomic 10 ℂ).nextCoeff = -∑ z ∈ primitiveRoots 10 ℂ, z := by
    rw [hprod]
    exact prod_X_sub_C_nextCoeff (fun z : ℂ => z)
  have h3 : ∑ z ∈ primitiveRoots 10 ℂ, z = 1 := by
    have : -∑ z ∈ primitiveRoots 10 ℂ, z = -1 := by rw [← h2, h1]
    linear_combination -this
  rw [h3, moebius_ten]
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

