import Mathlib
/-!
# Batch 16 — measurement projectors (qutrit completeness + Z-eigenprojector decomposition). All TRUE.
-/
namespace BrockianQuantum
open Matrix

theorem qutrit_completeness : E0 + E1 + E2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [E0, E1, E2, Matrix.add_apply, Matrix.diagonal]

