import Mathlib
open Matrix Polynomial
namespace MS2.BSpec2

theorem C5_trace_zero : Matrix.trace (!![0,1,0,0,1;1,0,1,0,0;0,1,0,1,0;0,0,1,0,1;1,0,0,1,0] : Matrix (Fin 5) (Fin 5) ℝ) = 0 := by
  simp [Matrix.trace, Fin.sum_univ_succ]

/-- `2` is an eigenvalue of the 5-cycle adjacency matrix, witnessed by the all-ones vector. -/
