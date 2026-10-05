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
noncomputable def posIndex {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian) : ℕ :=
  letI := Classical.dec
  (Finset.univ.filter fun i => 0 < hA.eigenvalues i).card

/-- The number of eigenvalues of a Hermitian matrix that are strictly above `θ`. -/
noncomputable def posIndexAbove {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian) (θ : ℝ) : ℕ :=
  letI := Classical.dec
  (Finset.univ.filter fun i => θ < hA.eigenvalues i).card

/-- The (real) quadratic form associated with a matrix. -/
noncomputable def qform (M : Matrix (Fin d) (Fin d) ℂ) (x : EuclideanSpace ℂ (Fin d)) : ℝ :=
  (⟪x, Matrix.toEuclideanLin M x⟫_ℂ).re

lemma toEuclideanLin_eigenvectorBasis {M : Matrix (Fin d) (Fin d) ℂ} (hM : M.IsHermitian)
    (i : Fin d) :
    Matrix.toEuclideanLin M (hM.eigenvectorBasis i)
      = (hM.eigenvalues i : ℂ) • (hM.eigenvectorBasis i) := by
  have h := hM.mulVec_eigenvectorBasis i
  apply PiLp.ext
  intro j
  have h2 : (Matrix.toEuclideanLin M (hM.eigenvectorBasis i)).ofLp j
      = (M *ᵥ (hM.eigenvectorBasis i).ofLp) j := rfl
  rw [h2, h]
  simp [Complex.real_smul]

lemma inner_toEuclideanLin_eq_sum {M : Matrix (Fin d) (Fin d) ℂ} (hM : M.IsHermitian)
    (x : EuclideanSpace ℂ (Fin d)) :
    ⟪x, Matrix.toEuclideanLin M x⟫_ℂ =
      ∑ i, (hM.eigenvalues i : ℂ) * ((‖⟪hM.eigenvectorBasis i, x⟫_ℂ‖ : ℝ) : ℂ) ^ 2 := by
  have h1 : Matrix.toEuclideanLin M x
      = ∑ i, ((hM.eigenvalues i : ℂ) * ⟪hM.eigenvectorBasis i, x⟫_ℂ) • (hM.eigenvectorBasis i) := by
    conv_lhs => rw [← hM.eigenvectorBasis.sum_repr x]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, toEuclideanLin_eigenvectorBasis hM i, smul_smul,
      OrthonormalBasis.repr_apply_apply, mul_comm]
  rw [h1, inner_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_smul_right, ← inner_conj_symm x (hM.eigenvectorBasis i), mul_assoc,
    RCLike.mul_conj]
  norm_num

lemma qform_eq_sum {M : Matrix (Fin d) (Fin d) ℂ} (hM : M.IsHermitian)
    (x : EuclideanSpace ℂ (Fin d)) :
    qform M x = ∑ i, hM.eigenvalues i * ‖⟪hM.eigenvectorBasis i, x⟫_ℂ‖ ^ 2 := by
  rw [qform, inner_toEuclideanLin_eq_sum hM x, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  norm_cast

lemma qform_add (M N : Matrix (Fin d) (Fin d) ℂ) (x : EuclideanSpace ℂ (Fin d)) :
    qform (M + N) x = qform M x + qform N x := by
  simp [qform, Complex.add_re]

/-- If all eigenvalues of `M` are at most `θ`, the quadratic form is bounded by `θ‖x‖²`. -/
lemma qform_le_of_eigenvalues_le {M : Matrix (Fin d) (Fin d) ℂ} (hM : M.IsHermitian) {θ : ℝ}
    (hle : ∀ i, hM.eigenvalues i ≤ θ) (x : EuclideanSpace ℂ (Fin d)) :
    qform M x ≤ θ * ‖x‖ ^ 2 := by
  rw [qform_eq_sum hM, ← hM.eigenvectorBasis.sum_sq_norm_inner_right x, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_right (hle i) (by positivity)

/-- If `x` is orthogonal to all eigenvectors with positive eigenvalue, the quadratic form
is nonpositive. -/
lemma qform_nonpos_of_orthogonal {M : Matrix (Fin d) (Fin d) ℂ} (hM : M.IsHermitian)
    {x : EuclideanSpace ℂ (Fin d)}
    (hx : ∀ i, 0 < hM.eigenvalues i → ⟪hM.eigenvectorBasis i, x⟫_ℂ = 0) :
    qform M x ≤ 0 := by
  rw [qform_eq_sum hM]
  refine Finset.sum_nonpos fun i _ => ?_
  rcases lt_or_ge 0 (hM.eigenvalues i) with h | h
  · rw [hx i h]
    simp
  · exact mul_nonpos_of_nonpos_of_nonneg h (by positivity)

/-- If every eigenvector component of a nonzero `x` corresponds to an eigenvalue above `θ`,
then the quadratic form is strictly above `θ‖x‖²`. -/
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
theorem weyl_posIndexAbove {A E : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.IsHermitian) (hE : E.IsHermitian) (θ : ℝ)
    (hbound : ∀ i, |hE.eigenvalues i| ≤ θ) :
    posIndexAbove (hA.add hE) θ ≤ posIndex hA := by
  classical
  set hAE : (A + E).IsHermitian := hA.add hE
  set S : Finset (Fin d) := Finset.univ.filter fun i => θ < hAE.eigenvalues i with hS
  set P : Finset (Fin d) := Finset.univ.filter fun i => 0 < hA.eigenvalues i with hP
  -- the linear map sending coefficients to a vector in the span of the "high" eigenvectors
  set f : ({i // i ∈ S} → ℂ) →ₗ[ℂ] EuclideanSpace ℂ (Fin d) :=
    Fintype.linearCombination ℂ (fun i : {i // i ∈ S} => hAE.eigenvectorBasis i) with hf
  set g : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] ({j // j ∈ P} → ℂ) :=
    LinearMap.pi fun j : {j // j ∈ P} => (innerSL ℂ (hA.eigenvectorBasis j)).toLinearMap with hg
  have hEle : ∀ i, hE.eigenvalues i ≤ θ := fun i =>
    le_trans (le_abs_self _) (hbound i)
  have hinj : Function.Injective (g ∘ₗ f) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    set x : EuclideanSpace ℂ (Fin d) := f c with hx
    -- the eigen-components of `x`
    have hcomp : ∀ i : Fin d, ⟪hAE.eigenvectorBasis i, x⟫_ℂ
        = if h : i ∈ S then c ⟨i, h⟩ else 0 := by
      intro i
      rw [hx, hf, Fintype.linearCombination_apply, inner_sum]
      simp only [inner_smul_right,
        orthonormal_iff_ite.mp hAE.eigenvectorBasis.orthonormal]
      by_cases h : i ∈ S
      · rw [dif_pos h,
          Finset.sum_eq_single_of_mem (⟨i, h⟩ : {i // i ∈ S}) (Finset.mem_univ _)]
        · simp
        · intro j _ hj
          have hij : i ≠ (j : Fin d) := fun hcc => hj (Subtype.ext hcc.symm)
          simp [hij]
      · rw [dif_neg h]
        refine Finset.sum_eq_zero fun j _ => ?_
        have hij : i ≠ (j : Fin d) := fun hcc => h (hcc ▸ j.2)
        simp [hij]
    by_contra hcne
    -- `x` is nonzero
    have hxne : x ≠ 0 := by
      intro h0
      refine hcne (funext fun j => ?_)
      have := hcomp (j : Fin d)
      rw [h0, dif_pos j.2] at this
      simpa [Subtype.coe_eta] using this.symm
    -- `x` is orthogonal to the positive eigenvectors of `A`
    have hgx : g x = 0 := hc
    have horth : ∀ i, 0 < hA.eigenvalues i → ⟪hA.eigenvectorBasis i, x⟫_ℂ = 0 := by
      intro i hi
      have hiP : i ∈ P := by simp [hP, hi]
      have := congrFun hgx ⟨i, hiP⟩
      simpa [hg] using this
    have hAle : qform A x ≤ 0 := qform_nonpos_of_orthogonal hA horth
    have hEbound : qform E x ≤ θ * ‖x‖ ^ 2 := qform_le_of_eigenvalues_le hE hEle x
    have hgt : θ * ‖x‖ ^ 2 < qform (A + E) x := by
      refine qform_gt_of_components hAE hxne fun i hi => ?_
      by_cases h : i ∈ S
      · simpa [hS] using h
      · rw [hcomp i, dif_neg h] at hi
        exact absurd rfl hi
    rw [qform_add] at hgt
    linarith
  have hcard := LinearMap.finrank_le_finrank_of_injective hinj
  simpa [Module.finrank_fintype_fun_eq_card, Fintype.card_subtype, posIndex, posIndexAbove, hS, hP]
    using hcard

end Zeta23Redux.LinAlg

