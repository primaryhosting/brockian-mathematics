/-
# Mobius Root Sum 10
Category: Pure Mathematics
Target: Math.mobius_root_sum_10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 requires `import` commands to precede any module docstring, so the header above is
-- repeated as a module docstring immediately after the import.)

import Mathlib

/-!
# Mobius Root Sum 10
Category: Pure Mathematics
Target: Math.mobius_root_sum_10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Math

open Polynomial

/-- The tenth cyclotomic polynomial over `ℤ` is `X ^ 4 - X ^ 3 + X ^ 2 - X + 1`. -/
theorem cyclotomic_ten_int : cyclotomic 10 ℤ = X ^ 4 - X ^ 3 + X ^ 2 - X + 1 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h5 : cyclotomic 5 ℤ = X ^ 4 + X ^ 3 + X ^ 2 + X + 1 := by
    rw [cyclotomic_prime]
    simp [Finset.sum_range_succ]
    ring
  refine ((eq_cyclotomic_iff (R := ℤ) (n := 10) (by norm_num) _).mpr ?_).symm
  have h : Nat.properDivisors 10 = {1, 2, 5} := by decide
  rw [h]
  simp [cyclotomic_one, h5]
  ring

/-- The tenth cyclotomic polynomial over `ℂ`. -/
theorem cyclotomic_ten_complex : cyclotomic 10 ℂ = X ^ 4 - X ^ 3 + X ^ 2 - X + 1 := by
  have := congrArg (Polynomial.map (Int.castRingHom ℂ)) cyclotomic_ten_int
  rw [map_cyclotomic] at this
  simpa using this

/-- The Möbius function at `10` equals `1`. -/
theorem moebius_ten : ArithmeticFunction.moebius 10 = 1 := by
  rw [ArithmeticFunction.moebius_apply_of_squarefree (by decide +kernel)]
  norm_num [ArithmeticFunction.cardFactors_apply,
    show Nat.primeFactorsList 10 = [2, 5] from by decide +kernel]

/-- **Möbius root sum for `n = 10`.**  The sum of the primitive `10`-th roots of unity in `ℂ`
equals `μ 10` (which is `1`).

The key ingredient is `Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots`, which expresses the
`10`-th cyclotomic polynomial as `∏ μ ∈ primitiveRoots 10 ℂ, (X - C μ)`; the sum of the roots is
then read off from its next-to-leading coefficient via `Polynomial.prod_X_sub_C_nextCoeff`. -/
theorem mobius_root_sum_10 :
    ∑ z ∈ primitiveRoots 10 ℂ, z = (ArithmeticFunction.moebius 10 : ℂ) := by
  have hz : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / 10)) 10 :=
    Complex.isPrimitiveRoot_exp 10 (by norm_num)
  have hprod : cyclotomic 10 ℂ = ∏ w ∈ primitiveRoots 10 ℂ, (X - C w) :=
    cyclotomic_eq_prod_X_sub_primitiveRoots hz
  have hnext : nextCoeff (cyclotomic 10 ℂ) = -∑ z ∈ primitiveRoots 10 ℂ, z := by
    rw [hprod]
    exact prod_X_sub_C_nextCoeff (fun w => w)
  have hd : (X ^ 4 - X ^ 3 + X ^ 2 - X + 1 : ℂ[X]).natDegree = 4 := by compute_degree!
  have hnext' : nextCoeff (cyclotomic 10 ℂ) = -1 := by
    rw [cyclotomic_ten_complex, nextCoeff, if_neg (by rw [hd]; norm_num), hd]
    simp [coeff_one, coeff_X]
  rw [hnext'] at hnext
  rw [moebius_ten]
  push_cast
  linear_combination hnext

end Math

