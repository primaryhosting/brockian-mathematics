import Mathlib
open Matrix
namespace C5.QI7

theorem ghz_norm : (GHZᴴ * GHZ) 0 0 = 2 := by
  simp [GHZ, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ]
  norm_num

