import Mathlib
open Matrix
namespace C4.QC6

theorem X_hermitian : Xᴴ = X := by
  rw [X]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

end C4.QC6

