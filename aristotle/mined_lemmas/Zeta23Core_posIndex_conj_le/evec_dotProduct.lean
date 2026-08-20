import Mathlib

/-!
# Pos Index Conj Le
Category: Brockian Corpus
Target: Zeta23Core.posIndex_conj_le
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix Module Submodule

namespace Zeta23Core

variable {𝕜 : Type*} [RCLike 𝕜] {m d : Type*} [Fintype m] [DecidableEq m] [Fintype d]

/-- The (real) quadratic form `x ↦ xᴴ Q x` associated with a square matrix `Q`. -/

lemma evec_dotProduct {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian) (i j : m) :
    star (evec hQ i) ⬝ᵥ evec hQ j = if i = j then 1 else 0 := by
  have h := (orthonormal_iff_ite.1 hQ.eigenvectorBasis.orthonormal) i j
  rw [EuclideanSpace.inner_eq_star_dotProduct] at h
  simpa [evec, dotProduct_comm] using h

