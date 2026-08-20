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

lemma posDefOn_eigenSpan_posSet {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian) :
    PosDefOn Q (eigenSpan hQ (posSet hQ)) := by
  intro x hx hx0
  rw [qform_eq_sum hQ]
  refine Finset.sum_pos' (fun i _ => ?_) ?_
  · by_cases hi : i ∈ posSet hQ
    · have hpos : 0 < hQ.eigenvalues i := by simpa [posSet] using hi
      positivity
    · rw [inner_eq_zero_of_mem_eigenSpan hQ _ hx hi]
      simp
  · obtain ⟨i, hi⟩ : ∃ i, inner 𝕜 (hQ.eigenvectorBasis i) x ≠ 0 := by
      by_contra h
      push_neg at h
      exact hx0 (eq_zero_of_inner_eigenvectorBasis_eq_zero hQ x h)
    have hiP : i ∈ posSet hQ := by
      by_contra hc
      exact hi (inner_eq_zero_of_mem_eigenSpan hQ _ hx hc)
    have hpos : 0 < hQ.eigenvalues i := by simpa [posSet] using hiP
    refine ⟨i, Finset.mem_univ i, ?_⟩
    have hnorm : 0 < ‖inner 𝕜 (hQ.eigenvectorBasis i) x‖ ^ 2 := by positivity
    positivity

/-- `Q` is nonpositive on the span of the eigenvectors with nonpositive eigenvalue. -/
