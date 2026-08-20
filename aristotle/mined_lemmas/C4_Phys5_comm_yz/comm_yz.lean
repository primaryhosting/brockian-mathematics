import Mathlib
open Matrix
namespace C4.Phys5

theorem comm_yz : Sy*Sz - Sz*Sy = (2*Complex.I) • Sx := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Sx, Sy, Sz] <;> ring

