import Mathlib
/-!
# Batch 16 — measurement projectors (qutrit completeness + Z-eigenprojector decomposition). All TRUE.
-/
namespace BrockianQuantum
open Matrix

theorem E0_E1_orthogonal : E0 * E1 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [E0, E1, Matrix.mul_apply, Matrix.diagonal]

