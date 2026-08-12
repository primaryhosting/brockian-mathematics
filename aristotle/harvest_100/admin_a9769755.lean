/-
# Det Eq Mertens 4
Category: Frontier Wave 2 (deeper machinery)
Target: Riemann.Redheffer.det_eq_mertens_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Riemann.Redheffer

/-- The `4 × 4` Redheffer matrix: `R i j = 1` if `j = 0` or `(i+1) ∣ (j+1)`,
and `R i j = 0` otherwise (indices are `0`-based). -/
def R : Matrix (Fin 4) (Fin 4) ℤ :=
  Matrix.of fun i j => if (j : ℕ) = 0 ∨ ((i : ℕ) + 1) ∣ ((j : ℕ) + 1) then 1 else 0

/-- The Mertens function `M n = ∑_{k ≤ n} μ k`. -/
def mertens (n : ℕ) : ℤ := ∑ k ∈ Finset.Icc 1 n, (ArithmeticFunction.moebius k : ℤ)

/-- `M 4 = μ 1 + μ 2 + μ 3 + μ 4 = 1 - 1 - 1 + 0 = -1`. -/
theorem mertens_four : mertens 4 = -1 := by
  rw [mertens, show Finset.Icc 1 4 = ({1, 2, 3, 4} : Finset ℕ) from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton,
    ArithmeticFunction.moebius_eq_zero_of_not_squarefree (n := 4) (by decide),
    ArithmeticFunction.moebius_apply_prime Nat.prime_two,
    ArithmeticFunction.moebius_apply_prime Nat.prime_three]
  simp

/-- The determinant of the `4 × 4` Redheffer matrix equals `-1`. -/
theorem det_R_eq_neg_one : R.det = -1 := by
  simp [R, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.submatrix]
  decide

/-- **Redheffer's identity in size 4**: the determinant of the `4 × 4` Redheffer matrix
equals the Mertens function at `4`, namely `-1`. -/
theorem det_eq_mertens_4 : R.det = mertens 4 ∧ R.det = -1 :=
  ⟨by rw [det_R_eq_neg_one, mertens_four], det_R_eq_neg_one⟩

end Riemann.Redheffer

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

