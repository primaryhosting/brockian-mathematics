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

/-
# Weyl Pos Index Above
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.weyl_posIndexAbove
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Matrix Finset

namespace Zeta23Redux.LinAlg

variable {d : ℕ}

/-- The number of strictly positive eigenvalues of a Hermitian matrix. -/

lemma qform_gt_of_repr_eq_zero {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian) {θ : ℝ}
    (x : EuclideanSpace ℂ (Fin d)) (hx0 : x ≠ 0)
    (hx : ∀ i, (hA.eigenvectorBasis.repr x).ofLp i ≠ 0 → θ < hA.eigenvalues i) :
    θ * ‖x‖ ^ 2 < qform A x := by
  rw [qform_eq_sum hA x, norm_sq_eq_sum hA x, Finset.mul_sum]
  have hne : ∃ i : Fin d, (hA.eigenvectorBasis.repr x).ofLp i ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hx0 (by
      have : hA.eigenvectorBasis.repr x = 0 := by
        ext i; simpa using hcon i
      simpa using congrArg hA.eigenvectorBasis.repr.symm this)
  obtain ⟨j, hj⟩ := hne
  refine Finset.sum_lt_sum (fun i _ => ?_) ⟨j, Finset.mem_univ j, ?_⟩
  · rcases eq_or_ne ((hA.eigenvectorBasis.repr x).ofLp i) 0 with hi | hi
    · simp [hi]
    · exact mul_le_mul_of_nonneg_right (le_of_lt (hx i hi)) (by positivity)
  · have hpos : (0:ℝ) < ‖(hA.eigenvectorBasis.repr x).ofLp j‖ ^ 2 := by
      have : ‖(hA.eigenvectorBasis.repr x).ofLp j‖ ≠ 0 := by simpa using hj
      positivity
    exact mul_lt_mul_of_pos_right (hx j hj) hpos

/-- The vector with prescribed coordinates in an orthonormal basis, supported on `S`. -/
