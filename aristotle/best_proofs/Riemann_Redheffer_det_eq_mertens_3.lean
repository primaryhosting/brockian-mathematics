import Mathlib

/-!
# Det Eq Mertens 3
Category: Frontier Wave 2 (deeper machinery)
Target: Riemann.Redheffer.det_eq_mertens_3
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

namespace Riemann
namespace Redheffer

/-- The `3 × 3` Redheffer matrix (0-indexed): the entry in row `i`, column `j` is `1`
if `j = 0` or if `i + 1` divides `j + 1`, and `0` otherwise. -/
def R : Matrix (Fin 3) (Fin 3) ℤ :=
  Matrix.of fun i j => if (j : ℕ) = 0 ∨ ((i : ℕ) + 1) ∣ ((j : ℕ) + 1) then 1 else 0

/-- The determinant of the `3 × 3` Redheffer matrix equals the Mertens function
`M 3 = μ 1 + μ 2 + μ 3 = 1 - 1 - 1 = -1`. -/
theorem det_eq_mertens_3 : R.det = -1 := by
  have h : R = Matrix.of ![![1, 1, 1], ![1, 1, 0], ![1, 0, 1]] := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [h, Matrix.det_fin_three]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]

/-- The determinant of the `3 × 3` Redheffer matrix is literally the Mertens function at `3`,
i.e. the sum `∑_{n ≤ 3} μ n`. -/
theorem det_eq_sum_moebius_three :
    R.det = ∑ n ∈ Finset.Icc 1 3, ArithmeticFunction.moebius n := by
  have h2 : ArithmeticFunction.moebius 2 = -1 :=
    ArithmeticFunction.moebius_apply_prime Nat.prime_two
  have h3 : ArithmeticFunction.moebius 3 = -1 :=
    ArithmeticFunction.moebius_apply_prime Nat.prime_three
  rw [det_eq_mertens_3]
  simp [Finset.sum_Icc_succ_top, h2, h3]

end Redheffer
end Riemann

