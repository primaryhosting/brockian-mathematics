import Mathlib
open Matrix
namespace C5.Ph6

theorem sy_hermitian : Syᴴ = Sy := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Sy, Matrix.conjTranspose]

