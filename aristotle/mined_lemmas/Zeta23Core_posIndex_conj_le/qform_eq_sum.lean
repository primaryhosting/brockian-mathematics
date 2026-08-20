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

lemma qform_eq_sum {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian) (x : EuclideanSpace 𝕜 m) :
    qform Q x = ∑ i, hQ.eigenvalues i * ‖inner 𝕜 (hQ.eigenvectorBasis i) x‖ ^ 2 := by
  rw [qform, ← (hQ.eigenvectorBasis).sum_inner_mul_inner x (Matrix.toEuclideanLin Q x), map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_eigenvectorBasis_apply hQ i x, ← inner_conj_symm (𝕜 := 𝕜) (hQ.eigenvectorBasis i) x]
  set c : 𝕜 := inner 𝕜 x (hQ.eigenvectorBasis i) with hc
  rw [show c * ((hQ.eigenvalues i : 𝕜) * (starRingEnd 𝕜) c)
      = (hQ.eigenvalues i : 𝕜) * (c * (starRingEnd 𝕜) c) by ring, RCLike.mul_conj]
  simp

