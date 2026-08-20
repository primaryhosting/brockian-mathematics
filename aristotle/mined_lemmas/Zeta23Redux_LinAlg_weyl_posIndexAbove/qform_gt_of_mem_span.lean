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
open scoped Classical

namespace Zeta23Redux.LinAlg

open Matrix

variable {d : ℕ}

/-- The real quadratic form `x ↦ ⟪x, M x⟫` attached to a matrix `M`. -/

lemma qform_gt_of_mem_span {M : Matrix (Fin d) (Fin d) ℂ} (hM : M.IsHermitian) {theta : ℝ}
    {x : EuclideanSpace ℂ (Fin d)}
    (hx : x ∈ Submodule.span ℂ
      (hM.eigenvectorBasis '' ((Finset.univ.filter fun i => theta < hM.eigenvalues i) :
        Set (Fin d))))
    (hx0 : x ≠ 0) : theta * ‖x‖ ^ 2 < qform M x := by
  classical
  set s : Finset (Fin d) := Finset.univ.filter fun i => theta < hM.eigenvalues i with hs
  set w : Fin d → ℝ := fun i => ‖(inner ℂ (hM.eigenvectorBasis i) x : ℂ)‖ ^ 2 with hw
  have hwnonneg : ∀ i, 0 ≤ w i := fun i => by positivity
  have hzero : ∀ i ∉ s, w i = 0 := by
    intro i hi
    simp [hw, inner_eq_zero_of_mem_span hM hx hi]
  have hnorm : ‖x‖ ^ 2 = ∑ i, w i := norm_sq_eq_sum hM.eigenvectorBasis x
  have hpos : 0 < ∑ i, w i := by
    rw [← hnorm]
    have : 0 < ‖x‖ := norm_pos_iff.2 hx0
    positivity
  obtain ⟨i0, -, hi0⟩ : ∃ i ∈ Finset.univ, 0 < w i := by
    by_contra hcon
    push_neg at hcon
    exact absurd (Finset.sum_nonpos fun i hi => hcon i hi) (not_le.2 hpos)
  have hi0s : i0 ∈ s := by
    by_contra hmem
    exact absurd (hzero i0 hmem) (ne_of_gt hi0)
  rw [qform_eq_sum hM, hnorm, Finset.mul_sum]
  refine Finset.sum_lt_sum (fun i _ => ?_) ⟨i0, Finset.mem_univ _, ?_⟩
  · by_cases hi : i ∈ s
    · have : theta < hM.eigenvalues i := by
        rw [hs] at hi; simpa using hi
      exact mul_le_mul_of_nonneg_right this.le (hwnonneg i)
    · rw [hzero i hi, inner_eq_zero_of_mem_span hM hx hi]; simp
  · have h1 : theta < hM.eigenvalues i0 := by rw [hs] at hi0s; simpa using hi0s
    exact mul_lt_mul_of_pos_right h1 hi0

/-- On the span of eigenvectors with eigenvalue `≤ 0`, the form is `≤ 0`. -/
