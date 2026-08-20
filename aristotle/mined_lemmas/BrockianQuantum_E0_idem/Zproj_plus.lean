import Mathlib
/-!
# Batch 16 — measurement projectors (qutrit completeness + Z-eigenprojector decomposition). All TRUE.
-/
namespace BrockianQuantum
open Matrix

theorem Zproj_plus : (1 : Matrix (Fin 2) (Fin 2) ℂ) + PZ = (2 : ℂ) • P0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [P0, PZ, Matrix.add_apply, Matrix.smul_apply]; norm_num

