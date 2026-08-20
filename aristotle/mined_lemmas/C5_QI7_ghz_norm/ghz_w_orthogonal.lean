import Mathlib
open Matrix
namespace C5.QI7

theorem ghz_w_orthogonal : (GHZᴴ * W) 0 0 = 0 := by
  simp [GHZ, W, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ]

end C5.QI7

