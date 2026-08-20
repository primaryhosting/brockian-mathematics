import Mathlib
open Matrix Polynomial
namespace C2.BSpec3

theorem P7_eigen_center : P7.charpoly.eval 2 = 0 := by
  rw [Matrix.eval_charpoly, ← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨![1, 0, -1, 0, 1, 0, -1], ?_, ?_⟩
  · intro hv
    have := congrFun hv 0
    norm_num at this
  · funext i
    fin_cases i <;>
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, P7, Matrix.scalar_apply]

