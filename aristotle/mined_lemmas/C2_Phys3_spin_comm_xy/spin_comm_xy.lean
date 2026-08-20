import Mathlib
open Matrix
namespace C2.Phys3

theorem spin_comm_xy : Sx * Sy - Sy * Sx = (2*Complex.I) • Sz := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Sx, Sy, Sz, Complex.ext_iff] <;> ring

