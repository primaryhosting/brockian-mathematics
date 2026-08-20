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

/-!
## Inertia does not increase under compression

For a Hermitian matrix `Q` on a finite type `m` and a rectangular matrix `B : Matrix m d 𝕜`, the
compression `Bᴴ * Q * B` is Hermitian and its positive index of inertia (the number of positive
eigenvalues, counted with multiplicity) is at most that of `Q`.

The proof follows the variational route.  Writing `qform Q x = Re (xᴴ Q x)`, we prove both
directions of the (finite dimensional) Sylvester characterisation of the positive index:

* `Zeta23Core.exists_posdef_matrix`: the column space of `U * posProj` — where `U` diagonalises `Q`
  and `posProj` projects onto the positive eigen-directions — is a subspace of dimension
  `posIndex Q` on which `qform Q` is positive definite;
* `Zeta23Core.finrank_le_posIndex`: any subspace on which `qform Q` is positive definite has
  dimension at most `posIndex Q` (it meets the "non-positive" subspace `ker (posProj * Uᴴ)`
  trivially, and that kernel has codimension `posIndex Q`).

For the compression, such a subspace for `Bᴴ Q B` is pushed forward by `B`; injectivity on it is
forced by positive definiteness, so the dimension is preserved.
-/

namespace Zeta23Core

open Matrix Module

section Defs

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The (real) quadratic form `x ↦ Re (xᴴ Q x)` attached to a matrix `Q`. -/

lemma exists_posdef_matrix {Q : Matrix n n 𝕜} (hQ : Q.IsHermitian) :
    ∃ C : Matrix n n 𝕜, C.rank = posIndex Q ∧ ∀ c : n → 𝕜, C *ᵥ c ≠ 0 → 0 < qform Q (C *ᵥ c) := by
  set U : Matrix n n 𝕜 := (hQ.eigenvectorUnitary : Matrix n n 𝕜) with hUdef
  refine ⟨U * posProj hQ, ?_, ?_⟩
  · rw [Matrix.rank_mul_eq_right_of_isUnit_det _ _ (Matrix.UnitaryGroup.det_isUnit _),
      rank_posProj]
  · intro c hc
    have hy : star U *ᵥ ((U * posProj hQ) *ᵥ c) = posProj hQ *ᵥ c := by
      rw [mulVec_mulVec, ← Matrix.mul_assoc, UnitaryGroup.star_mul_self, Matrix.one_mul]
    rw [qform_eq_sum hQ, ← hUdef, hy]
    have hne : posProj hQ *ᵥ c ≠ 0 := by
      intro h
      exact hc (by rw [← mulVec_mulVec, h, mulVec_zero])
    obtain ⟨j, hj⟩ : ∃ j, (posProj hQ *ᵥ c) j ≠ 0 := by
      by_contra h
      push_neg at h
      exact hne (funext h)
    have hjpos : 0 < hQ.eigenvalues j := by
      by_contra h
      exact hj (by simp [posProj, mulVec_diagonal, h])
    refine Finset.sum_pos' (fun i _ => ?_) ⟨j, Finset.mem_univ j, ?_⟩
    · rcases lt_or_ge 0 (hQ.eigenvalues i) with h | h
      · positivity
      · have hz : (posProj hQ *ᵥ c) i = 0 := by simp [posProj, mulVec_diagonal, not_lt.2 h]
        simp [hz]
    · have hpos : (0 : ℝ) < ‖(posProj hQ *ᵥ c) j‖ ^ 2 := by positivity
      exact mul_pos hjpos hpos

/-- **Hard direction of Sylvester's law**: any subspace on which the form of `Q` is positive
definite has dimension at most `posIndex Q`. -/
