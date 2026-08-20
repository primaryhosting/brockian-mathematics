import Mathlib
open Matrix
namespace C3.QC5

theorem hadamard_sq2 : H * H = (2:ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [H, Matrix.mul_apply, Fin.sum_univ_two]

