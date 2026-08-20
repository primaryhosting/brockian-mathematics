import Mathlib
/-!
# Batch 10 — density matrices, projectors, Pauli traces. All TRUE; bare import Mathlib.
-/
namespace BrockianQuantum
open Matrix

theorem P0_idem : P0 * P0 = P0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [P0, Matrix.mul_apply, Fin.sum_univ_two]

