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
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Zeta23Redux.LinAlg

open Matrix Finset

variable {d : ℕ}

/-- The real quadratic form `x ↦ re ⟪x, M x⟫` associated to a matrix `M`. -/

lemma qform_gt_of_inner_eq_zero {M : Matrix (Fin d) (Fin d) ℂ} (hM : M.IsHermitian)
    (s : Finset (Fin d)) {c : ℝ} (h : ∀ i ∈ s, c < hM.eigenvalues i)
    {x : EuclideanSpace ℂ (Fin d)} (hx : ∀ i ∉ s, inner ℂ (hM.eigenvectorBasis i) x = 0)
    (hx0 : x ≠ 0) :
    c * ‖x‖ ^ 2 < qform M x := by
  set t : Fin d → ℝ := fun i => ‖inner ℂ (hM.eigenvectorBasis i) x‖ ^ 2 with ht
  have hsum : ∑ i, t i = ‖x‖ ^ 2 := hM.eigenvectorBasis.sum_sq_norm_inner_right x
  have hpos : 0 < ∑ i, (hM.eigenvalues i - c) * t i := by
    refine Finset.sum_pos' (fun i _ => ?_) ?_
    · by_cases hi : i ∈ s
      · exact mul_nonneg (by linarith [h i hi]) (by positivity)
      · simp [ht, hx i hi]
    · have hxn : 0 < ‖x‖ ^ 2 := by positivity
      rw [← hsum] at hxn
      obtain ⟨i, -, hi⟩ := Finset.exists_lt_of_sum_lt
        (by simpa using hxn : ∑ _i : Fin d, (0:ℝ) < ∑ i, t i)
      have hmem : i ∈ s := by
        by_contra hc
        simp [ht, hx i hc] at hi
      exact ⟨i, Finset.mem_univ i, mul_pos (by linarith [h i hmem]) hi⟩
  rw [qform_eq hM]
  have hrw : ∑ i, (hM.eigenvalues i - c) * t i = (∑ i, hM.eigenvalues i * t i) - c * ‖x‖ ^ 2 := by
    rw [← hsum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  linarith [hrw ▸ hpos]

/-- A vector in the span of a subfamily of an orthonormal basis is orthogonal to the remaining
basis vectors. -/
