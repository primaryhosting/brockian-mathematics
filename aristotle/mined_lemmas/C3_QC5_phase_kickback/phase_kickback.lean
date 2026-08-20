import Mathlib
open Matrix
namespace C3.QC5

theorem phase_kickback : X * (!![1;1] : Matrix (Fin 2) (Fin 1) ℂ) = !![1;1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [X, Matrix.mul_apply, Fin.sum_univ_two]

