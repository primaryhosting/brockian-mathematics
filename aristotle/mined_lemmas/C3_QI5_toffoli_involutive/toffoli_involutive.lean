import Mathlib
open Matrix
namespace C3.QI5

theorem toffoli_involutive : CCX * CCX = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CCX, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The CNOT gate is an involution. -/
