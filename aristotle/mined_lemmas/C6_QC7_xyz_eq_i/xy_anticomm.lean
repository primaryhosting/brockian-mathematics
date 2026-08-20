import Mathlib
open Matrix
namespace C6.QC7

theorem xy_anticomm : X*Y + Y*X = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [X, Y]
end C6.QC7

