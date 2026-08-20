import Mathlib
/-!
# Batch 16 — measurement projectors (qutrit completeness + Z-eigenprojector decomposition). All TRUE.
-/
namespace BrockianQuantum
open Matrix

theorem E1_idem : E1 * E1 = E1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [E1, Matrix.mul_apply, Matrix.diagonal]

