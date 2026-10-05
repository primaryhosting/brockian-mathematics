/-
# Mobius Root Sum 9
Category: Pure Mathematics
Target: Math.mobius_root_sum_9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Polynomial Finset

namespace Math

/-- The sum of the primitive `9`-th roots of unity in `ℂ` equals `μ 9` (which is `0`).

The proof identifies the sum with (minus) the coefficient of `X ^ 5` in the ninth
cyclotomic polynomial `Φ₉ = X ^ 6 + X ^ 3 + 1`, via
`Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots` and
`Polynomial.prod_X_sub_C_coeff_card_pred`. -/
theorem mobius_root_sum_9 :
    ∑ z ∈ primitiveRoots 9 ℂ, z = (ArithmeticFunction.moebius 9 : ℂ) := by
  have hzeta : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / 9)) 9 :=
    Complex.isPrimitiveRoot_exp 9 (by norm_num)
  have hcard : #(primitiveRoots 9 ℂ) = 6 := by
    rw [hzeta.card_primitiveRoots]; decide
  have h1 : (cyclotomic 9 ℂ).coeff 5 = -∑ z ∈ primitiveRoots 9 ℂ, z := by
    rw [cyclotomic_eq_prod_X_sub_primitiveRoots hzeta]
    have h := prod_X_sub_C_coeff_card_pred (primitiveRoots 9 ℂ) (fun z => z)
      (by rw [hcard]; norm_num)
    rw [hcard] at h
    simpa using h
  have h2 : cyclotomic 9 ℂ = ∑ i ∈ range 3, (X ^ 3) ^ i := by
    have h : (9 : ℕ) = 3 ^ (1 + 1) := by norm_num
    rw [h, cyclotomic_prime_pow_eq_geom_sum (by norm_num)]
    norm_num
  rw [h2] at h1
  have h3 : (∑ i ∈ range 3, ((X : ℂ[X]) ^ 3) ^ i).coeff 5 = 0 := by
    simp [Finset.sum_range_succ, coeff_one, ← pow_mul, coeff_X_pow]
  rw [h3] at h1
  have hm : ArithmeticFunction.moebius 9 = 0 :=
    ArithmeticFunction.moebius_eq_zero_of_not_squarefree
      (fun h => by simpa using h 3 ⟨1, by norm_num⟩)
  rw [hm]
  simpa using neg_eq_zero.mp h1.symm

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

