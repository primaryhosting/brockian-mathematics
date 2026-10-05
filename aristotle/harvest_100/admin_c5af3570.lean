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

/-- The `5 × 5` Redheffer matrix over `ℤ`, using `0`-indexed `Fin 5`:
the entry in row `i`, column `j` is `1` when `j = 0` or `(i+1) ∣ (j+1)`, and `0` otherwise. -/
def R5 : Matrix (Fin 5) (Fin 5) ℤ :=
  Matrix.of fun i j => if j = 0 ∨ ((i : ℕ) + 1) ∣ ((j : ℕ) + 1) then 1 else 0

/-- Explicit entries of the `5 × 5` Redheffer matrix. -/
theorem R5_eq :
    R5 = !![1, 1, 1, 1, 1;
            1, 1, 0, 1, 0;
            1, 0, 1, 0, 0;
            1, 0, 0, 1, 0;
            1, 0, 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [R5]

/-- The determinant of the `5 × 5` Redheffer matrix equals the Mertens function
`M(5) = μ(1) + μ(2) + μ(3) + μ(4) + μ(5) = 1 - 1 - 1 + 0 - 1 = -2`. -/
set_option maxRecDepth 100000 in
theorem det_eq_mertens_5 : R5.det = -2 := by
  rw [R5_eq]
  norm_num [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove, Fin.lt_def]

end Redheffer
end Riemann

