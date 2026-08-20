import Mathlib
open Matrix
namespace C3.QI5

theorem cnot_sq : CNOT * CNOT = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CNOT, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The determinant of CNOT is `-1` (it is a single transposition). -/
