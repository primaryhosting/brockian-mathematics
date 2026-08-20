import Mathlib
open Matrix Polynomial
namespace MS2.BSpec2

theorem pentagon_eigen_two : (!![0,1,0,0,1;1,0,1,0,0;0,1,0,1,0;0,0,1,0,1;1,0,0,1,0] : Matrix (Fin 5) (Fin 5) ℝ).charpoly.eval 2 = 0 := by
  rw [Matrix.eval_charpoly, ← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨fun _ => 1, ?_, ?_⟩
  · intro h
    have := congrFun h 0
    simp at this
  · funext i
    fin_cases i <;>
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Matrix.scalar_apply] <;> ring

