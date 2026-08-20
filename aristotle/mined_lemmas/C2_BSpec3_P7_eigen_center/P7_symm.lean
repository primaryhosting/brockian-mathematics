import Mathlib
open Matrix Polynomial
namespace C2.BSpec3

theorem P7_symm : P7.IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [P7, Matrix.transpose_apply]

