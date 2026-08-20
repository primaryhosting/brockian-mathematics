import Mathlib
namespace Frontier.BrockianNextLevel

theorem pentagon_trace_zero :
    Matrix.trace (!![0,1,0,0,1; 1,0,1,0,0; 0,1,0,1,0; 0,0,1,0,1; 1,0,0,1,0] : Matrix (Fin 5) (Fin 5) ℝ) = 0 := by
  simp [Matrix.trace, Fin.sum_univ_succ]
