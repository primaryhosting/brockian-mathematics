import Mathlib
open Matrix Polynomial
namespace BrockianFrontier.PentagonSpectrum

/-- Adjacency matrix of the 5-cycle Cā‚… (the pentagon graph). -/

theorem C6_eigenvalue_neg_two :
    C6.charpoly.eval (-2) = 0 := by
  -- The alternating vector is an eigenvector for the eigenvalue `-2`.
  rw [Matrix.eval_charpoly, ← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨![1, -1, 1, -1, 1, -1], ?_, ?_⟩
  · intro h
    have := congrFun h 0
    norm_num at this
  · funext i
    fin_cases i <;>
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, C6, Matrix.scalar] <;> norm_num

end BrockianFrontier.PentagonSpectrum

