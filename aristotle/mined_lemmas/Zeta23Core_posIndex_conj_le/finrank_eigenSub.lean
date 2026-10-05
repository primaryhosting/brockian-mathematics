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

open Matrix Module

variable {𝕜 : Type*} [RCLike 𝕜] {m d : Type*} [Fintype m] [DecidableEq m]
  [Fintype d] [DecidableEq d]

/-- The (real) quadratic form associated with a matrix `Q`: `x ↦ Re (xᴴ Q x)`. -/

lemma finrank_eigenSub {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian) (s : Finset m) :
    finrank 𝕜 (eigenSub hQ s) = s.card := by
  rw [eigenSub, ← (Submodule.equivMapOfInjective _ (mulVecLin_eigenvectorUnitary_injective hQ)
    (coordSub s)).finrank_eq, finrank_coordSub]

/-- On the span of the eigenvectors with positive eigenvalue, `Q` is positive definite. -/
