import Mathlib
open Matrix
namespace MS2.QI3

theorem hadamard_unnorm_sq : H2 * H2 = (2:ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [H2, Matrix.mul_apply, Fin.sum_univ_succ] <;> norm_num

