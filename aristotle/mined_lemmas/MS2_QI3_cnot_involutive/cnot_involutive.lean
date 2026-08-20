import Mathlib
open Matrix
namespace MS2.QI3

theorem cnot_involutive : CNOT * CNOT = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CNOT, Matrix.mul_apply, Fin.sum_univ_succ]

