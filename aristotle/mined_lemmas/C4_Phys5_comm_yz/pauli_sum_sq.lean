import Mathlib
open Matrix
namespace C4.Phys5

theorem pauli_sum_sq : Sx*Sx + Sy*Sy + Sz*Sz = (3:ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Sx, Sy, Sz, Complex.I_mul_I] <;> norm_num
end C4.Phys5

