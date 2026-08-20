import Mathlib
open Matrix
namespace MS2.QI3

theorem xz_eq_neg_zx : X * Z = - (Z * X) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [X, Z, Matrix.mul_apply, Fin.sum_univ_succ]

