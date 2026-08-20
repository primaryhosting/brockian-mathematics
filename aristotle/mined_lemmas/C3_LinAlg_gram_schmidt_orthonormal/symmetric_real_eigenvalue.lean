import Mathlib

open InnerProductSpace

namespace C3.LinAlg

/-- Gram–Schmidt applied to a linearly independent family produces an orthonormal family. -/

theorem symmetric_real_eigenvalue {n : ℕ} (hn : 0 < n) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsSymm) :
    ∃ (v : EuclideanSpace ℝ (Fin n)) (l : ℝ), v ≠ 0 ∧ Matrix.toEuclideanLin A v = l • v := by
  have hH : A.IsHermitian := hA
  refine ⟨hH.eigenvectorBasis ⟨0, hn⟩, hH.eigenvalues ⟨0, hn⟩,
    hH.eigenvectorBasis.orthonormal.ne_zero _, ?_⟩
  have h := hH.mulVec_eigenvectorBasis ⟨0, hn⟩
  ext i
  have h2 := congrFun h i
  simpa [Matrix.toEuclideanLin, Matrix.mulVec, dotProduct] using h2

/-- The trace of a matrix is the sum of its diagonal entries. -/
