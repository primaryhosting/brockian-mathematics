import Mathlib
open Matrix
namespace C2.Phys3

def Sx : Matrix (Fin 2) (Fin 2) ℂ := !![0,1;1,0]

def Sy : Matrix (Fin 2) (Fin 2) ℂ := !![0,-Complex.I;Complex.I,0]

def Sz : Matrix (Fin 2) (Fin 2) ℂ := !![1,0;0,-1]

theorem spin_comm_xy : Sx * Sy - Sy * Sx = (2*Complex.I) • Sz := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Sx, Sy, Sz, Complex.ext_iff] <;> ring
