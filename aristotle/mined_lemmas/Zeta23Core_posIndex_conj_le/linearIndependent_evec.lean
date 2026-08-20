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

lemma linearIndependent_evec {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian) :
    LinearIndependent 𝕜 (evec hQ) :=
  hQ.eigenvectorBasis.orthonormal.linearIndependent.map'
    (WithLp.linearEquiv 2 𝕜 (m → 𝕜)).toLinearMap (by simp)

/-- The quadratic form evaluated on a linear combination of eigenvectors. -/
