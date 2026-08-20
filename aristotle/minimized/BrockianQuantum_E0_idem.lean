import Mathlib
/-!
# Batch 16 — measurement projectors (qutrit completeness + Z-eigenprojector decomposition). All TRUE.
-/
namespace BrockianQuantum
open Matrix

def E0 : Matrix (Fin 3) (Fin 3) ℂ := Matrix.diagonal ![1,0,0]

theorem E0_idem : E0 * E0 = E0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [E0, Matrix.mul_apply, Matrix.diagonal]
