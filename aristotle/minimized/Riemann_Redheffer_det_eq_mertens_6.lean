import Mathlib
/-!
# Det Eq Mertens 6
Category: Frontier Wave 2 (deeper machinery)
Target: Riemann.Redheffer.det_eq_mertens_6
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

/-- The `6 × 6` Redheffer matrix: `R i j = 1` if `j = 0` or `(i+1) ∣ (j+1)`,
and `R i j = 0` otherwise. -/

def R : Matrix (Fin 6) (Fin 6) ℤ :=
  fun i j => if (j : ℕ) = 0 ∨ ((i : ℕ) + 1) ∣ ((j : ℕ) + 1) then 1 else 0

/-- Explicit description of the `6 × 6` Redheffer matrix. -/

lemma R_eq :
    R = !![1, 1, 1, 1, 1, 1;
           1, 1, 0, 1, 0, 1;
           1, 0, 1, 0, 0, 1;
           1, 0, 0, 1, 0, 0;
           1, 0, 0, 0, 1, 0;
           1, 0, 0, 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [R]

/-- The determinant of the `6 × 6` Redheffer matrix equals the Mertens function
`M(6) = -1`. -/

theorem det_eq_mertens_6 : R.det = -1 := by
  rw [R_eq]
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]

/-- Restatement: `det R = M(6) = M(5) + μ(6) = -2 + 1 = -1`. -/
