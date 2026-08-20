import Mathlib
open Matrix
namespace C4.QC6

theorem S_sq_eq_Z : S * S = !![1,0;0,-1] := by
  rw [S, Matrix.mul_fin_two]
  simp [Complex.I_mul_I]

