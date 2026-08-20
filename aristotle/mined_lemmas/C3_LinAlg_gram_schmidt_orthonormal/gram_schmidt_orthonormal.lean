import Mathlib

open InnerProductSpace

namespace C3.LinAlg

/-- Gram–Schmidt applied to a linearly independent family produces an orthonormal family. -/

theorem gram_schmidt_orthonormal {n : ℕ} (v : Fin n → EuclideanSpace ℝ (Fin n))
    (hv : LinearIndependent ℝ v) :
    ∃ w : Fin n → EuclideanSpace ℝ (Fin n), Orthonormal ℝ w :=
  ⟨gramSchmidtNormed ℝ v, gramSchmidtNormed_orthonormal hv⟩

/-- A real symmetric matrix on a nonempty index type has a (real) eigenvalue with a nonzero
eigenvector. -/
