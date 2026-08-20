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

lemma finrank_eigenSpan {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian) (T : Finset m) :
    Module.finrank 𝕜 (eigenSpan hQ T) = T.card := by
  have hli : LinearIndependent 𝕜 (fun i : {i // i ∈ T} => hQ.eigenvectorBasis i) :=
    (hQ.eigenvectorBasis.orthonormal.comp _ Subtype.val_injective).linearIndependent
  have hrange : Set.range (fun i : {i // i ∈ T} => hQ.eigenvectorBasis i)
      = hQ.eigenvectorBasis '' (T : Set m) := by
    ext y
    simp [Set.mem_range, Set.mem_image]
  rw [eigenSpan, ← hrange, finrank_span_eq_card hli, Fintype.card_coe]

