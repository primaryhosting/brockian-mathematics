import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

import Mathlib
/-!
# Weyl Pos Index Above
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.weyl_posIndexAbove
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped InnerProductSpace
open Matrix

namespace Zeta23Redux.LinAlg

variable {d : ℕ}

/-- The number of strictly positive eigenvalues of a Hermitian matrix. -/

lemma qform_gt_of_components {M : Matrix (Fin d) (Fin d) ℂ} (hM : M.IsHermitian) {θ : ℝ}
    {x : EuclideanSpace ℂ (Fin d)} (hx0 : x ≠ 0)
    (hx : ∀ i, ⟪hM.eigenvectorBasis i, x⟫_ℂ ≠ 0 → θ < hM.eigenvalues i) :
    θ * ‖x‖ ^ 2 < qform M x := by
  have hsum : ∑ i, ‖⟪hM.eigenvectorBasis i, x⟫_ℂ‖ ^ 2 = ‖x‖ ^ 2 :=
    hM.eigenvectorBasis.sum_sq_norm_inner_right x
  have hxpos : 0 < ‖x‖ ^ 2 := by positivity
  have hex : ∃ i ∈ Finset.univ, 0 < ‖⟪hM.eigenvectorBasis i, x⟫_ℂ‖ ^ 2 := by
    by_contra hcon
    push_neg at hcon
    have : ∑ i, ‖⟪hM.eigenvectorBasis i, x⟫_ℂ‖ ^ 2 ≤ 0 :=
      Finset.sum_nonpos fun i hi => hcon i hi
    rw [hsum] at this
    exact absurd this (not_le.2 hxpos)
  have key : 0 < ∑ i, (hM.eigenvalues i - θ) * ‖⟪hM.eigenvectorBasis i, x⟫_ℂ‖ ^ 2 := by
    obtain ⟨i0, -, hi0⟩ := hex
    refine Finset.sum_pos' (fun i _ => ?_) ⟨i0, Finset.mem_univ i0, ?_⟩
    · rcases eq_or_ne (⟪hM.eigenvectorBasis i, x⟫_ℂ) 0 with h | h
      · rw [h]; simp
      · exact mul_nonneg (by linarith [hx i h]) (by positivity)
    · have hne : ⟪hM.eigenvectorBasis i0, x⟫_ℂ ≠ 0 := by
        intro h
        rw [h] at hi0
        simp at hi0
      exact mul_pos (by linarith [hx i0 hne]) hi0
  have hsplit : ∑ i, (hM.eigenvalues i - θ) * ‖⟪hM.eigenvectorBasis i, x⟫_ℂ‖ ^ 2
      = qform M x - θ * ‖x‖ ^ 2 := by
    rw [qform_eq_sum hM, ← hsum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  linarith [hsplit ▸ key]

/-- **Weyl monotonicity for the positive index.**
If `A` and `E` are Hermitian and every eigenvalue of `E` has absolute value at most `θ`,
then the number of eigenvalues of `A + E` strictly above `θ` is at most the number of
strictly positive eigenvalues of `A`. -/
