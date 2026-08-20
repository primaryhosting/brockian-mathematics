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

lemma finrank_le_posIndex {Q : Matrix n n 𝕜} (hQ : Q.IsHermitian)
    (S : Submodule 𝕜 (n → 𝕜)) (hS : ∀ x ∈ S, x ≠ 0 → 0 < qform Q x) :
    finrank 𝕜 S ≤ posIndex Q := by
  set U : Matrix n n 𝕜 := (hQ.eigenvectorUnitary : Matrix n n 𝕜) with hUdef
  have hdet : IsUnit (star U).det := by
    simpa [hUdef] using Matrix.UnitaryGroup.det_isUnit (star hQ.eigenvectorUnitary)
  set G : Matrix n n 𝕜 := posProj hQ * star U with hG
  set f : (n → 𝕜) →ₗ[𝕜] (n → 𝕜) := Matrix.mulVecLin G with hf
  have hker : ∀ x ∈ LinearMap.ker f, qform Q x ≤ 0 := by
    intro x hx
    rw [LinearMap.mem_ker, hf, Matrix.mulVecLin_apply, hG, ← mulVec_mulVec] at hx
    rw [qform_eq_sum hQ, ← hUdef]
    refine Finset.sum_nonpos fun i _ => ?_
    rcases lt_or_ge 0 (hQ.eigenvalues i) with h | h
    · have hz : (star U *ᵥ x) i = 0 := by
        simpa [posProj, mulVec_diagonal, h] using congrFun hx i
      simp [hz]
    · have hnn : (0 : ℝ) ≤ ‖(star U *ᵥ x) i‖ ^ 2 := by positivity
      exact mul_nonpos_of_nonpos_of_nonneg h hnn
  have hdisj : Disjoint S (LinearMap.ker f) := by
    rw [Submodule.disjoint_def]
    intro x hxS hxK
    by_contra hx
    exact absurd (hS x hxS hx) (not_lt.2 (hker x hxK))
  have h1 := Submodule.finrank_add_finrank_le_of_disjoint (K := 𝕜) (V := n → 𝕜) hdisj
  have h2 := LinearMap.finrank_range_add_finrank_ker (K := 𝕜) f
  have h3 : finrank 𝕜 (LinearMap.range f) = posIndex Q := by
    rw [← rank_posProj hQ]
    change G.rank = _
    rw [hG, Matrix.rank_mul_eq_left_of_isUnit_det (star U) (posProj hQ) hdet]
  omega

end Defs

variable {𝕜 : Type*} [RCLike 𝕜] {m d : Type*} [Fintype m] [DecidableEq m]
  [Fintype d] [DecidableEq d]

omit [DecidableEq m] [Fintype d] [DecidableEq d] in
/-- A compression of a Hermitian matrix is Hermitian. -/
