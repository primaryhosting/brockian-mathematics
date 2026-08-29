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

lemma exists_isPosOn {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian) :
    ∃ S : Submodule 𝕜 (m → 𝕜), IsPosOn Q S ∧ finrank 𝕜 S = posIndex Q := by
  refine ⟨eigenSub hQ (Finset.univ.filter fun i => 0 < hQ.eigenvalues i),
    isPosOn_eigenSub hQ, ?_⟩
  rw [finrank_eigenSub, posIndex, dif_pos hQ]

/-- Sylvester, hard direction: any subspace on which `Q` is positive definite has dimension at
most `posIndex Q`. -/
