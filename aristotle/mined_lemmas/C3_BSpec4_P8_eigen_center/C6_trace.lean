import Mathlib
open Matrix Polynomial
namespace C3.BSpec4

theorem C6_trace : Matrix.trace (!![0,1,0,0,0,1;1,0,1,0,0,0;0,1,0,1,0,0;0,0,1,0,1,0;0,0,0,1,0,1;1,0,0,0,1,0] : Matrix (Fin 6) (Fin 6) ℝ) = 0 := by
  simp [Matrix.trace, Matrix.diag, Fin.sum_univ_six]
end C3.BSpec4

