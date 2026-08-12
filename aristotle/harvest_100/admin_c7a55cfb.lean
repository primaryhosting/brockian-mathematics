/-
# Det Eq Mertens 5
Category: Frontier Wave 2 (deeper machinery)
Target: Riemann.Redheffer.det_eq_mertens_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Riemann
namespace Redheffer

/-- The `5 × 5` Redheffer matrix over `ℤ`, with rows and columns indexed by `Fin 5`
(0-indexed): the `(i, j)` entry is `1` if `j = 0` or `(i+1) ∣ (j+1)`, and `0` otherwise. -/
def R : Matrix (Fin 5) (Fin 5) ℤ :=
  Matrix.of fun i j => if j = 0 ∨ ((i : ℕ) + 1) ∣ ((j : ℕ) + 1) then 1 else 0

/-- Explicit description of the `5 × 5` Redheffer matrix. -/
lemma R_eq :
    R = !![1, 1, 1, 1, 1;
           1, 1, 0, 1, 0;
           1, 0, 1, 0, 0;
           1, 0, 0, 1, 0;
           1, 0, 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [R]

/-- The determinant of the `5 × 5` Redheffer matrix equals `M(5) = -2`, the Mertens
function at `5`. -/
theorem det_eq_mertens_5 : R.det = -2 := by
  rw [R_eq]
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  decide

/-- The determinant of the `5 × 5` Redheffer matrix equals the Mertens function
`M(5) = μ(1) + μ(2) + μ(3) + μ(4) + μ(5)`. -/
theorem det_eq_sum_moebius :
    R.det = ∑ k ∈ Finset.Icc 1 5, (ArithmeticFunction.moebius k : ℤ) := by
  have h4 : ArithmeticFunction.moebius 4 = 0 :=
    ArithmeticFunction.moebius_eq_zero_of_not_squarefree (by decide)
  rw [det_eq_mertens_5, show Finset.Icc 1 5 = ({1, 2, 3, 4, 5} : Finset ℕ) from rfl]
  norm_num [ArithmeticFunction.moebius_apply_prime, h4]

end Redheffer
end Riemann

