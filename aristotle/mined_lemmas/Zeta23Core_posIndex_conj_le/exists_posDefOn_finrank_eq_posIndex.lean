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

lemma exists_posDefOn_finrank_eq_posIndex {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian) :
    ∃ S : Submodule 𝕜 (EuclideanSpace 𝕜 m), Module.finrank 𝕜 S = posIndex Q ∧ PosDefOn Q S :=
  ⟨eigenSpan hQ (posSet hQ), by rw [finrank_eigenSpan, posIndex_eq_card],
    posDefOn_eigenSpan_posSet hQ⟩

/-- **Inertia does not increase under compression**: for a Hermitian matrix `Q` and any
rectangular matrix `B`, the compression `Bᴴ Q B` is Hermitian and `n₊(Bᴴ Q B) ≤ n₊(Q)`. -/
