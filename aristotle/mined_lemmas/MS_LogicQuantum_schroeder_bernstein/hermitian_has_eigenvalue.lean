import Mathlib
open Matrix
namespace MS.LogicQuantum


theorem hermitian_has_eigenvalue {n : ℕ} (hn : 0 < n) (M : Matrix (Fin n) (Fin n) ℂ)
    (hM : M.IsHermitian) : ∃ (v : EuclideanSpace ℂ (Fin n)) (μ : ℝ), v ≠ 0 ∧
      Matrix.toEuclideanLin M v = (μ : ℂ) • v := by
  let j : Fin n := ⟨0, hn⟩
  refine ⟨hM.eigenvectorBasis j, hM.eigenvalues j, hM.eigenvectorBasis.orthonormal.ne_zero j, ?_⟩
  have key : Matrix.toEuclideanLin M (hM.eigenvectorBasis j)
      = WithLp.toLp 2 (M *ᵥ (hM.eigenvectorBasis j).ofLp) := rfl
  rw [key, hM.mulVec_eigenvectorBasis j]
  ext k
  simp [Complex.real_smul]

end MS.LogicQuantum

