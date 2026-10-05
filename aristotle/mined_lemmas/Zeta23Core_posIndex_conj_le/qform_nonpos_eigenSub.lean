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

lemma qform_nonpos_eigenSub {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian)
    (x : m → 𝕜) (hx : x ∈ eigenSub hQ (Finset.univ.filter fun i => ¬ 0 < hQ.eigenvalues i)) :
    qform Q x ≤ 0 := by
  obtain ⟨y, hy, rfl⟩ := hx
  rw [Matrix.mulVecLin_apply, qform_eigen]
  refine Finset.sum_nonpos fun j _ => ?_
  by_cases hj : j ∈ Finset.univ.filter fun i => ¬ 0 < hQ.eigenvalues i
  · have h : hQ.eigenvalues j ≤ 0 := by
      have := (Finset.mem_filter.mp hj).2
      simpa using not_lt.mp this
    have h2 : (0:ℝ) ≤ ‖y j‖ ^ 2 := sq_nonneg _
    nlinarith
  · rw [hy j hj]; simp

/-- Existence of a positive definite subspace of dimension `posIndex Q`. -/
