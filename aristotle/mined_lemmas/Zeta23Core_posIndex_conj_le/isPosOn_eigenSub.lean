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

lemma isPosOn_eigenSub {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian) :
    IsPosOn Q (eigenSub hQ (Finset.univ.filter fun i => 0 < hQ.eigenvalues i)) := by
  rintro _ ⟨y, hy, rfl⟩ hne
  have hy0 : y ≠ 0 := by rintro rfl; simp at hne
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hy0
  rw [Matrix.mulVecLin_apply, qform_eigen]
  refine Finset.sum_pos' (fun j _ => ?_) ⟨i, Finset.mem_univ i, ?_⟩
  · by_cases hj : j ∈ Finset.univ.filter fun i => 0 < hQ.eigenvalues i
    · have : 0 < hQ.eigenvalues j := by simpa using (Finset.mem_filter.mp hj).2
      exact mul_nonneg this.le (sq_nonneg _)
    · rw [hy j hj]; simp
  · have hi' : i ∈ Finset.univ.filter fun i => 0 < hQ.eigenvalues i := by
      by_contra h
      exact hi (hy i h)
    have hpos : 0 < hQ.eigenvalues i := by simpa using (Finset.mem_filter.mp hi').2
    exact mul_pos hpos (pow_pos (norm_pos_iff.mpr hi) 2)

/-- On the span of the eigenvectors with non-positive eigenvalue, `Q` is negative semidefinite. -/
