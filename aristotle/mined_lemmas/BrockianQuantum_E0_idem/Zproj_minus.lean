import Mathlib
/-!
# Batch 16 — measurement projectors (qutrit completeness + Z-eigenprojector decomposition). All TRUE.
-/
namespace BrockianQuantum
open Matrix

theorem Zproj_minus : (1 : Matrix (Fin 2) (Fin 2) ℂ) - PZ = (2 : ℂ) • P1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [P1, PZ, Matrix.sub_apply, Matrix.smul_apply]; norm_num

end BrockianQuantum

