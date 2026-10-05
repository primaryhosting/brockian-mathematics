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

/-
# Det Eq Mertens 6
Category: Frontier Wave 2 (deeper machinery)
Target: Riemann.Redheffer.det_eq_mertens_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

set_option maxRecDepth 10000

namespace Riemann.Redheffer

/-- The `6 × 6` Redheffer matrix, with the `Fin 6` indices standing for `1, …, 6`:
the entry at `(i, j)` is `1` when `j = 0` (the first column) or when `i + 1` divides `j + 1`,
and `0` otherwise. -/
def R6 : Matrix (Fin 6) (Fin 6) ℤ :=
  Matrix.of fun i j => if j = 0 ∨ ((i : ℕ) + 1) ∣ ((j : ℕ) + 1) then 1 else 0

/-- Explicit entries of the `6 × 6` Redheffer matrix. -/
theorem R6_eq : R6 = Matrix.of ![![1, 1, 1, 1, 1, 1],
                                 ![1, 1, 0, 1, 0, 1],
                                 ![1, 0, 1, 0, 0, 1],
                                 ![1, 0, 0, 1, 0, 0],
                                 ![1, 0, 0, 0, 1, 0],
                                 ![1, 0, 0, 0, 0, 1]] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [R6]

/-- The determinant of the `6 × 6` Redheffer matrix equals the Mertens function
`M 6 = -2 + μ 6 = -1`. -/
theorem det_eq_mertens_6 : R6.det = -1 := by
  rw [R6_eq]
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.cons_val', Matrix.cons_val_fin_one, Fin.succAbove]

end Riemann.Redheffer

#print axioms Riemann.Redheffer.det_eq_mertens_6

