import Mathlib

/-!
# Det Eq Mertens 5
Category: Frontier Wave 2 (deeper machinery)
Target: Riemann.Redheffer.det_eq_mertens_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Riemann.Redheffer

/-- The `5 × 5` Redheffer matrix over `ℤ`, with `0`-indexed rows and columns:
`R i j = 1` when the column index is `0` (i.e. the entry lies in the first column)
or when `i + 1` divides `j + 1`, and `R i j = 0` otherwise. -/
def R : Matrix (Fin 5) (Fin 5) ℤ :=
  fun i j => if j.val = 0 ∨ (i.val + 1) ∣ (j.val + 1) then 1 else 0

/-- The explicit entries of the `5 × 5` Redheffer matrix. -/
theorem R_eq : R = !![1, 1, 1, 1, 1;
                      1, 1, 0, 1, 0;
                      1, 0, 1, 0, 0;
                      1, 0, 0, 1, 0;
                      1, 0, 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- The determinant of the `5 × 5` Redheffer matrix equals `-2`. -/
theorem det_eq_mertens_5 : R.det = -2 := by
  simp only [Matrix.det_succ_row_zero, Fin.sum_univ_succ, R, Matrix.submatrix_apply,
    Fin.sum_univ_zero]
  decide

/-- The Mertens function at `5`, i.e. `μ(1) + μ(2) + μ(3) + μ(4) + μ(5) = 1 - 1 - 1 + 0 - 1`,
equals `-2`. -/
theorem mertens_5 : ∑ k ∈ Finset.Icc 1 5, (ArithmeticFunction.moebius k : ℤ) = -2 := by
  have h1 : (ArithmeticFunction.moebius 1 : ℤ) = 1 := by simp
  have h2 : (ArithmeticFunction.moebius 2 : ℤ) = -1 :=
    ArithmeticFunction.moebius_apply_prime (by norm_num)
  have h3 : (ArithmeticFunction.moebius 3 : ℤ) = -1 :=
    ArithmeticFunction.moebius_apply_prime (by norm_num)
  have h4 : (ArithmeticFunction.moebius 4 : ℤ) = 0 := by decide
  have h5 : (ArithmeticFunction.moebius 5 : ℤ) = -1 :=
    ArithmeticFunction.moebius_apply_prime (by norm_num)
  simp [Finset.sum_Icc_succ_top, h1, h2, h3, h4, h5]

/-- The Redheffer determinant identity for `n = 5`: `det R = M(5)`. -/
theorem det_eq_mertens_sum_5 :
    R.det = ∑ k ∈ Finset.Icc 1 5, (ArithmeticFunction.moebius k : ℤ) := by
  rw [det_eq_mertens_5, mertens_5]

end Riemann.Redheffer

