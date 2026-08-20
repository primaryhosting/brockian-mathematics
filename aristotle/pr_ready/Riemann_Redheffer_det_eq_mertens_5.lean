/-!
# Det Eq Mertens 5
Category: Frontier Wave 2 (deeper machinery)
Target: Riemann.Redheffer.det_eq_mertens_5
Statement: The 5x5 Redheffer matrix R (R i j = 1 if j=0 or (i+1) divides (j+1), else 0, over the integers, 0-indexed Fin 5) has det R = -2 = M(5) = mu(1)+mu(2)+mu(3)+mu(4)+mu(5) = 1-1-1+0-1 = -2. Prove det R = -2.
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Riemann.Redheffer

/-- The `5 × 5` Redheffer matrix over `ℤ` (0-indexed): the entry in row `i`, column `j`
is `1` when `j = 0` or when `i + 1` divides `j + 1`, and `0` otherwise. -/
def R5 : Matrix (Fin 5) (Fin 5) ℤ :=
  Matrix.of fun i j => if (j : ℕ) = 0 ∨ ((i : ℕ) + 1) ∣ ((j : ℕ) + 1) then 1 else 0

/-- Explicit entries of the `5 × 5` Redheffer matrix. -/
theorem R5_eq :
    R5 = !![1, 1, 1, 1, 1;
            1, 1, 0, 1, 0;
            1, 0, 1, 0, 0;
            1, 0, 0, 1, 0;
            1, 0, 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [R5]

/-- The determinant of the `5 × 5` Redheffer matrix equals the Mertens function value
`M(5) = μ(1) + μ(2) + μ(3) + μ(4) + μ(5) = 1 - 1 - 1 + 0 - 1 = -2`. -/
theorem det_eq_mertens_5 : R5.det = -2 := by
  rw [R5_eq]
  simp only [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.submatrix_apply,
    Finset.univ_eq_empty, Finset.sum_empty]
  decide

/-- The determinant of the `5 × 5` Redheffer matrix agrees with the Mertens sum
`∑_{n=1}^{5} μ(n)`. -/
theorem det_eq_mertens_sum_5 :
    R5.det = ∑ n ∈ Finset.Icc 1 5, (ArithmeticFunction.moebius n : ℤ) := by
  have h4 : ArithmeticFunction.moebius 4 = 0 := by
    rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree]
    decide
  rw [det_eq_mertens_5]
  simp [Finset.sum_Icc_succ_top, ArithmeticFunction.moebius_apply_prime,
    show Nat.Prime 2 by norm_num, show Nat.Prime 3 by norm_num, show Nat.Prime 5 by norm_num, h4]

end Riemann.Redheffer

