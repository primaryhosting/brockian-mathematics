/-
# Weyl Pos Index Above
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.weyl_posIndexAbove
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Weyl Pos Index Above
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.weyl_posIndexAbove
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
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Zeta23Redux.LinAlg

open Matrix

variable {d : ℕ}

/-- The number of strictly positive eigenvalues of a Hermitian matrix. -/

lemma qform_gt_of_mem_span {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian) {θ : ℝ}
    {s : Finset (Fin d)} (hs : ∀ i ∈ s, θ < hA.eigenvalues i)
    {x : EuclideanSpace ℂ (Fin d)}
    (hx : x ∈ Submodule.span ℂ (hA.eigenvectorBasis '' (s : Set (Fin d)))) (hx0 : x ≠ 0) :
    θ * ‖x‖ ^ 2 < qform A x := by
  have hzero : ∀ i ∉ s, ‖inner ℂ (hA.eigenvectorBasis i) x‖ ^ 2 = 0 := by
    intro i hi
    simp [inner_eq_zero_of_mem_span hA.eigenvectorBasis s hx hi]
  have hsum : ‖x‖ ^ 2 = ∑ i ∈ s, ‖inner ℂ (hA.eigenvectorBasis i) x‖ ^ 2 := by
    rw [norm_sq_eq_sum hA]
    exact (Finset.sum_subset (Finset.subset_univ s) fun i _ hi => hzero i hi).symm
  have hq : qform A x
      = ∑ i ∈ s, hA.eigenvalues i * ‖inner ℂ (hA.eigenvectorBasis i) x‖ ^ 2 := by
    rw [qform_eq hA]
    refine (Finset.sum_subset (Finset.subset_univ s) fun i _ hi => ?_).symm
    rw [hzero i hi, mul_zero]
  have hpos : 0 < ∑ i ∈ s, ‖inner ℂ (hA.eigenvectorBasis i) x‖ ^ 2 := by
    rw [← hsum]
    exact pow_pos (norm_pos_iff.mpr hx0) 2
  obtain ⟨i₀, hi₀s, hi₀⟩ : ∃ i ∈ s, 0 < ‖inner ℂ (hA.eigenvectorBasis i) x‖ ^ 2 := by
    by_contra hcon
    push_neg at hcon
    have hle : ∑ i ∈ s, ‖inner ℂ (hA.eigenvectorBasis i) x‖ ^ 2 ≤ 0 :=
      Finset.sum_nonpos fun i hi => hcon i hi
    linarith
  rw [hq, hsum, Finset.mul_sum]
  refine Finset.sum_lt_sum (fun i hi => ?_) ⟨i₀, hi₀s, ?_⟩
  · exact mul_le_mul_of_nonneg_right (le_of_lt (hs i hi)) (sq_nonneg _)
  · exact mul_lt_mul_of_pos_right (hs i₀ hi₀s) hi₀

/-- If all coefficients along positive eigenvectors vanish, the quadratic form is nonpositive. -/
