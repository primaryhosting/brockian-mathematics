import Mathlib
open Matrix
namespace C4.Phys5

theorem comm_zx : Sz*Sx - Sx*Sz = (2*Complex.I) • Sy := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Sx, Sy, Sz] <;> ring_nf <;> simp [Complex.I_sq]

