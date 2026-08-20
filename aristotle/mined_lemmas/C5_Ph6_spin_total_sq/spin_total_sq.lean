import Mathlib
open Matrix
namespace C5.Ph6

theorem spin_total_sq : Sx*Sx+Sy*Sy+Sz*Sz = (3:ℂ)•(1:Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Sx, Sy, Sz, Matrix.one_fin_two, Complex.I_mul_I] <;> ring

