import Mathlib
/-!
# Batch 10 — density matrices, projectors, Pauli traces. All TRUE; bare import Mathlib.
-/
namespace BrockianQuantum
open Matrix

theorem completeness : P0 + P1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [P0, P1, Matrix.add_apply]

