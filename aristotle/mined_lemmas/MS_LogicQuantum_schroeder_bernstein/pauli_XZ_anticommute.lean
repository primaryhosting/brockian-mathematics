import Mathlib
open Matrix
namespace MS.LogicQuantum


theorem pauli_XZ_anticommute :
    (!![0,1;1,0] : Matrix (Fin 2) (Fin 2) ℂ) * !![1,0;0,-1]
      = - (!![1,0;0,-1] * !![0,1;1,0]) := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_fin_two]

/-- Spectral theorem (finite Hermitian matrices are unitarily diagonalizable — existence of an
    orthonormal eigenbasis). -/
