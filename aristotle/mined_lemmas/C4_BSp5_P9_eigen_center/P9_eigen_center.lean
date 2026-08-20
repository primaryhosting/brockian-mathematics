import Mathlib
open Matrix Polynomial
namespace C4.BSp5

theorem P9_eigen_center : P9.charpoly.eval 2 = 0 := by
  rw [Matrix.eval_charpoly, ← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨![1, 0, -1, 0, 1, 0, -1, 0, 1], ?_, ?_⟩
  · intro h
    have := congrFun h 0
    norm_num at this
  · funext i
    fin_cases i <;>
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, P9, Matrix.scalar]

