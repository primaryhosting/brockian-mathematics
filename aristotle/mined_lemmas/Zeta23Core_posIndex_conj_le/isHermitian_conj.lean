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
open scoped Classical
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

variable {𝕜 : Type*} [RCLike 𝕜] {m d : Type*} [Fintype m] [Fintype d]

/-- The real quadratic form associated with a matrix: `x ↦ re (xᴴ Q x)`. -/

lemma isHermitian_conj {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian) (B : Matrix m d 𝕜) :
    (Bᴴ * Q * B).IsHermitian := by
  simp [Matrix.IsHermitian, Matrix.conjTranspose_mul, hQ.eq, Matrix.mul_assoc]

/-- The unitary `V` of eigenvectors diagonalizes `Q`: `Vᴴ Q V` is the diagonal matrix of
eigenvalues. -/
