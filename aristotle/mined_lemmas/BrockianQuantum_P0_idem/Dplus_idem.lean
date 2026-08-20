import Mathlib
/-!
# Batch 10 — density matrices, projectors, Pauli traces. All TRUE; bare import Mathlib.
-/
namespace BrockianQuantum
open Matrix

theorem Dplus_idem : Dplus * Dplus = Dplus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Dplus, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

