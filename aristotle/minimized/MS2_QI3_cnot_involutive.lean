import Mathlib
open Matrix
namespace MS2.QI3

def CNOT : Matrix (Fin 4) (Fin 4) ℂ := !![1,0,0,0;0,1,0,0;0,0,0,1;0,0,1,0]

theorem cnot_involutive : CNOT * CNOT = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CNOT, Matrix.mul_apply, Fin.sum_univ_succ]
