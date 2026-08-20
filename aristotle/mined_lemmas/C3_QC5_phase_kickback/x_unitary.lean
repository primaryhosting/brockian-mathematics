import Mathlib
open Matrix
namespace C3.QC5

theorem x_unitary : X * Xᴴ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [X, Matrix.mul_apply, Fin.sum_univ_two]
end C3.QC5

