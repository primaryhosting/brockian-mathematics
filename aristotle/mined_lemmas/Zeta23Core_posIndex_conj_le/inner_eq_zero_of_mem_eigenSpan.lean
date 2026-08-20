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

lemma inner_eq_zero_of_mem_eigenSpan {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian) (T : Finset m)
    {x : EuclideanSpace 𝕜 m} (hx : x ∈ eigenSpan hQ T) {i : m} (hi : i ∉ T) :
    inner 𝕜 (hQ.eigenvectorBasis i) x = 0 := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨j, hj, rfl⟩ := hy
      have hij : i ≠ j := by rintro rfl; exact hi hj
      exact hQ.eigenvectorBasis.orthonormal.2 hij
  | zero => simp
  | add y z _ _ hy hz => simp [inner_add_right, hy, hz]
  | smul a y _ hy => simp [inner_smul_right, hy]

/-- The set of indices of positive eigenvalues. -/
