import Mathlib

/-!
# Pos Index Conj Le
Category: Brockian Corpus
Target: Zeta23Core.posIndex_conj_le
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Zeta23Core

open Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {m d : Type*} [Fintype m] [DecidableEq m] [Fintype d]
  [DecidableEq d]

/-- Unfolding lemma for `Matrix.toEuclideanLin`. -/

lemma eq_zero_of_inner_eigenvectorBasis_eq_zero {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian)
    (x : EuclideanSpace 𝕜 m) (h : ∀ i, inner 𝕜 (hQ.eigenvectorBasis i) x = 0) : x = 0 := by
  have hrepr : hQ.eigenvectorBasis.repr x = 0 := by
    ext i
    rw [OrthonormalBasis.repr_apply_apply]
    simp [h i]
  simpa using hQ.eigenvectorBasis.repr.injective (by simpa using hrepr)

/-- The span of the eigenvectors indexed by a finite set `T`. -/
