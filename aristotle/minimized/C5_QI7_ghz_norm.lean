import Mathlib
open Matrix
namespace C5.QI7

def GHZ : Matrix (Fin 8) (Fin 1) ℂ := !![1;0;0;0;0;0;0;1]

theorem ghz_norm : (GHZᴴ * GHZ) 0 0 = 2 := by
  simp [GHZ, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ]
  norm_num
