import Mathlib
open Matrix
namespace MS2.QI3

theorem pauli_z_involutive : Z * Z = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Z, Matrix.mul_apply, Fin.sum_univ_succ]
end MS2.QI3

