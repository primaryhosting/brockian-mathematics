import Mathlib
open Matrix
namespace C5.QI7

theorem w_norm : (Wᴴ * W) 0 0 = 3 := by
  simp [W, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ]
  norm_num

