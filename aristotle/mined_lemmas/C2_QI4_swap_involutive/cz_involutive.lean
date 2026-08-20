import Mathlib
open Matrix
namespace C2.QI4

theorem cz_involutive : CZ * CZ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CZ, Matrix.mul_apply, Fin.sum_univ_four]

