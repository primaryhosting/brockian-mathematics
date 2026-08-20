import Mathlib
open Matrix
namespace C6.QC7

theorem xyz_eq_i : X*Y*Z = Complex.I • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [X, Y, Z, Matrix.mul_apply, Fin.sum_univ_succ]

