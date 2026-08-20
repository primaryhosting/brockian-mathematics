import Mathlib
open Matrix
namespace C2.QI4

theorem swap_involutive : SWAP * SWAP = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SWAP, Matrix.mul_apply, Fin.sum_univ_four]

