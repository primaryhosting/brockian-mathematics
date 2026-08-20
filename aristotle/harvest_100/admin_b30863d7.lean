import Mathlib

/-!
# Sylvester Hermitian Finrank
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.sylvester_hermitian_finrank
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Matrix WithLp Finset

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

namespace Zeta23Redux.LinAlg

variable {d : ℕ} {A : Matrix (Fin d) (Fin d) ℂ}

/-- The *positive index* of a Hermitian matrix `A`: the number of strictly positive
eigenvalues of `A` (counted with multiplicity, i.e. the number of indices `i` with
`hA.eigenvalues i > 0`).  It depends on `A` only, but is phrased in terms of the
hermiticity witness `hA` since Mathlib's `Matrix.IsHermitian.eigenvalues` is. -/
noncomputable def posIndex (hA : A.IsHermitian) : ℕ :=
  #{i | 0 < hA.eigenvalues i}

/-- Diagonalisation of the Hermitian form: for a Hermitian matrix `A`, the value of the
sesquilinear form at `v` is `∑ i, λ i * ‖⟪bᵢ, v⟫‖ ^ 2`, where `λ` are the eigenvalues
and `b` is the eigenvector orthonormal basis. -/
theorem inner_mulVec_eq_sum_eigenvalues (hA : A.IsHermitian)
    (v : EuclideanSpace ℂ (Fin d)) :
    inner ℂ v (toLp 2 (A *ᵥ v.ofLp)) =
      ∑ i, (hA.eigenvalues i : ℂ) * ‖inner ℂ (hA.eigenvectorBasis i) v‖ ^ 2 := by
  have hv : ∑ i, ((hA.eigenvectorBasis).repr v).ofLp i • hA.eigenvectorBasis i = v :=
    hA.eigenvectorBasis.sum_repr v
  have hL : toLp 2 (A *ᵥ v.ofLp)
      = ∑ i, ((hA.eigenvectorBasis).repr v).ofLp i •
        ((hA.eigenvalues i : ℂ) • hA.eigenvectorBasis i) := by
    rw [← Matrix.toLpLin_apply 2 2 A v]
    conv_lhs => rw [← hv]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, Matrix.toLpLin_apply, hA.mulVec_eigenvectorBasis,
      RCLike.real_smul_eq_coe_smul (K := ℂ)]
    simp only [WithLp.toLp_smul, WithLp.toLp_ofLp]
    rfl
  rw [hL, inner_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_smul_right, inner_smul_right, hA.eigenvectorBasis.repr_apply_apply,
    ← Complex.mul_conj', ← inner_conj_symm (hA.eigenvectorBasis i) v, Complex.conj_conj]
  ring

/-- The Hermitian form written through the plain `dotProduct` notation. -/
theorem star_dotProduct_mulVec_eq_sum_eigenvalues (hA : A.IsHermitian) (x : Fin d → ℂ) :
    star x ⬝ᵥ (A *ᵥ x) =
      ((∑ i, hA.eigenvalues i * ‖inner ℂ (hA.eigenvectorBasis i) (toLp 2 x)‖ ^ 2 : ℝ) : ℂ) := by
  have h := inner_mulVec_eq_sum_eigenvalues hA (toLp 2 x)
  rw [EuclideanSpace.inner_eq_star_dotProduct] at h
  rw [dotProduct_comm] at h
  rw [h]
  push_cast
  rfl

/-- If all the "positive" eigen-coordinates of `x` vanish, then the Hermitian form is
nonpositive at `x`. -/
theorem re_star_dotProduct_mulVec_nonpos (hA : A.IsHermitian) (x : Fin d → ℂ)
    (hx : ∀ i, 0 < hA.eigenvalues i → inner ℂ (hA.eigenvectorBasis i) (toLp 2 x) = 0) :
    (star x ⬝ᵥ (A *ᵥ x)).re ≤ 0 := by
  rw [star_dotProduct_mulVec_eq_sum_eigenvalues hA x, Complex.ofReal_re]
  refine Finset.sum_nonpos fun i _ => ?_
  rcases le_or_gt (hA.eigenvalues i) 0 with h | h
  · exact mul_nonpos_of_nonpos_of_nonneg h (by positivity)
  · simp [hx i h]

/-- **Sylvester's law of inertia** (Hermitian case, the inequality direction used in the
paper): if the Hermitian form `x ↦ Re (star x ⬝ᵥ A *ᵥ x)` associated to a Hermitian matrix
`A` is positive definite on a subspace `W`, then `finrank W ≤ posIndex A`, the number of
strictly positive eigenvalues of `A`. -/
theorem sylvester_hermitian_finrank (hA : A.IsHermitian) (W : Submodule ℂ (Fin d → ℂ))
    (hW : ∀ x ∈ W, x ≠ 0 → 0 < (star x ⬝ᵥ (A *ᵥ x)).re) :
    Module.finrank ℂ W ≤ posIndex hA := by
  classical
  set P : Finset (Fin d) := {i | 0 < hA.eigenvalues i} with hP
  -- the ℂ-linear map sending `x` to its eigen-coordinates indexed by `P`
  set e : (Fin d → ℂ) ≃ₗ[ℂ] (Fin d → ℂ) :=
    ((WithLp.linearEquiv 2 ℂ (Fin d → ℂ)).symm.trans
      (hA.eigenvectorBasis.repr.toLinearEquiv)).trans
        (WithLp.linearEquiv 2 ℂ (Fin d → ℂ)) with he
  set T : (Fin d → ℂ) →ₗ[ℂ] ((i : {i // i ∈ P}) → ℂ) :=
    (LinearMap.funLeft ℂ ℂ (Subtype.val : {i // i ∈ P} → Fin d)).comp (e : (Fin d → ℂ) →ₗ[ℂ] _)
    with hT
  have hcoord : ∀ (x : Fin d → ℂ) (i : Fin d),
      e x i = inner ℂ (hA.eigenvectorBasis i) (toLp 2 x) := by
    intro x i
    simpa [he] using hA.eigenvectorBasis.repr_apply_apply (toLp 2 x) i
  have hinj : Function.Injective (T.domRestrict W) := by
    rw [← LinearMap.ker_eq_bot]
    refine LinearMap.ker_eq_bot'.2 ?_
    rintro ⟨x, hxW⟩ hx0
    have hx : ∀ i, 0 < hA.eigenvalues i → inner ℂ (hA.eigenvectorBasis i) (toLp 2 x) = 0 := by
      intro i hi
      have : T x ⟨i, by simp [hP, hi]⟩ = 0 := by
        rw [show T x = (T.domRestrict W) ⟨x, hxW⟩ from rfl, hx0]; rfl
      rw [← hcoord]
      simpa [hT, LinearMap.funLeft_apply] using this
    by_contra hne
    have hx' : x ≠ 0 := fun h => hne (Subtype.ext h)
    exact absurd (re_star_dotProduct_mulVec_nonpos hA x hx) (not_le.2 (hW x hxW hx'))
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at hle
  exact hle

end Zeta23Redux.LinAlg

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

