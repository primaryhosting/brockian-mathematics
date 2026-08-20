import Mathlib

/-!
# Weyl Pos Index Above
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.weyl_posIndexAbove
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Matrix

namespace Zeta23Redux.LinAlg

variable {d : ℕ}

/-- The real quadratic form `x ↦ ⟪x, M x⟫` associated to a matrix `M`
(taking the real part, which for Hermitian `M` loses no information). -/
noncomputable def qform (M : Matrix (Fin d) (Fin d) ℂ) (x : EuclideanSpace ℂ (Fin d)) : ℝ :=
  (inner ℂ x (Matrix.toEuclideanLin M x)).re

lemma qform_add (M N : Matrix (Fin d) (Fin d) ℂ) (x : EuclideanSpace ℂ (Fin d)) :
    qform (M + N) x = qform M x + qform N x := by
  simp [qform, map_add]

/-- The linear map of a Hermitian matrix acts on its eigenvector basis by scaling. -/
lemma toEuclideanLin_eigenvectorBasis {M : Matrix (Fin d) (Fin d) ℂ} (hM : M.IsHermitian)
    (i : Fin d) :
    Matrix.toEuclideanLin M (hM.eigenvectorBasis i)
      = (hM.eigenvalues i : ℂ) • hM.eigenvectorBasis i := by
  have h := hM.mulVec_eigenvectorBasis i
  ext j
  simp [Matrix.toLpLin_apply, h]

/-- Spectral expansion of the quadratic form of a Hermitian matrix. -/
lemma qform_eq_sum {M : Matrix (Fin d) (Fin d) ℂ} (hM : M.IsHermitian)
    (x : EuclideanSpace ℂ (Fin d)) :
    qform M x = ∑ i, hM.eigenvalues i * ‖(inner ℂ (hM.eigenvectorBasis i) x : ℂ)‖ ^ 2 := by
  have hsym : (Matrix.toEuclideanLin M).IsSymmetric := Matrix.isHermitian_iff_isSymmetric.1 hM
  have key : (inner ℂ x (Matrix.toEuclideanLin M x) : ℂ)
      = ∑ i, ((hM.eigenvalues i * ‖(inner ℂ (hM.eigenvectorBasis i) x : ℂ)‖ ^ 2 : ℝ) : ℂ) := by
    rw [← hM.eigenvectorBasis.sum_inner_mul_inner x (Matrix.toEuclideanLin M x)]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : (inner ℂ (hM.eigenvectorBasis i) (Matrix.toEuclideanLin M x) : ℂ)
        = (hM.eigenvalues i : ℂ) * inner ℂ (hM.eigenvectorBasis i) x := by
      rw [← hsym, toEuclideanLin_eigenvectorBasis hM i, inner_smul_left]
      simp
    rw [h1, ← inner_conj_symm (𝕜 := ℂ) (hM.eigenvectorBasis i) x, ← mul_assoc,
      mul_comm _ ((hM.eigenvalues i : ℂ)), mul_assoc]
    push_cast
    congr 1
    rw [mul_comm, RCLike.conj_mul]
    simp
    rw [norm_inner_symm]
  rw [qform, key, Complex.re_sum]
  simp only [Complex.ofReal_re]

/-- If all eigenvalues of a Hermitian matrix are at most `θ`, its quadratic form is
bounded by `θ ‖x‖²`. -/
lemma qform_le_of_eigenvalues_le {M : Matrix (Fin d) (Fin d) ℂ} (hM : M.IsHermitian) {θ : ℝ}
    (h : ∀ i, hM.eigenvalues i ≤ θ) (x : EuclideanSpace ℂ (Fin d)) :
    qform M x ≤ θ * ‖x‖ ^ 2 := by
  rw [qform_eq_sum hM, ← OrthonormalBasis.sum_sq_norm_inner_right hM.eigenvectorBasis x,
    Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (h i) (by positivity)

/-- The number of eigenvalues of a Hermitian matrix that are strictly above `θ`. -/
noncomputable def posIndexAbove {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian) (θ : ℝ) : ℕ :=
  {i | θ < hA.eigenvalues i}.toFinset.card

/-- The number of strictly positive eigenvalues of a Hermitian matrix. -/
noncomputable def posIndex {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian) : ℕ :=
  posIndexAbove hA 0

/-- **Weyl monotonicity**: if `A` and `E` are Hermitian and every eigenvalue of `E` has
absolute value at most `θ`, then the number of eigenvalues of `A + E` strictly above `θ`
is at most the number of strictly positive eigenvalues of `A`. -/
theorem weyl_posIndexAbove {A E : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian)
    (hE : E.IsHermitian) (θ : ℝ) (hEθ : ∀ i, |hE.eigenvalues i| ≤ θ) :
    posIndexAbove (hA.add hE) θ ≤ posIndex hA := by
  classical
  set hAE : (A + E).IsHermitian := hA.add hE with hAEdef
  set P : Finset (Fin d) := {i | (0:ℝ) < hA.eigenvalues i}.toFinset with hP
  set Q : Finset (Fin d) := {j | θ < hAE.eigenvalues j}.toFinset with hQ
  -- the linear map sending coefficients to the corresponding combination of eigenvectors
  set S : (↥Q → ℂ) →ₗ[ℂ] EuclideanSpace ℂ (Fin d) :=
    Fintype.linearCombination ℂ (fun j : ↥Q => hAE.eigenvectorBasis (j : Fin d)) with hS
  set R : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] (↥P → ℂ) :=
    LinearMap.pi (fun i : ↥P => (innerSL ℂ (hA.eigenvectorBasis (i : Fin d))).toLinearMap) with hR
  have hEle : ∀ i, hE.eigenvalues i ≤ θ := fun i =>
    le_trans (le_abs_self _) (hEθ i)
  have hinj : Function.Injective ⇑(R ∘ₗ S) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro f hf
    by_contra hfne
    -- the vector built from the coefficients
    set x : EuclideanSpace ℂ (Fin d) := S f with hx
    have hcoord : ∀ k : Fin d,
        (inner ℂ (hAE.eigenvectorBasis k) x : ℂ) = if h : k ∈ Q then f ⟨k, h⟩ else 0 := by
      intro k
      have hxeq : x = ∑ j : ↥Q, f j • hAE.eigenvectorBasis (j : Fin d) := by
        simp [hx, hS, Fintype.linearCombination_apply]
      rw [hxeq, inner_sum]
      have hterm : ∀ j : ↥Q, (inner ℂ (hAE.eigenvectorBasis k)
          (f j • hAE.eigenvectorBasis (j : Fin d)) : ℂ)
          = if k = (j : Fin d) then f j else 0 := by
        intro j
        rw [inner_smul_right, hAE.eigenvectorBasis.inner_eq_ite]
        split <;> simp_all
      simp only [hterm]
      by_cases hk : k ∈ Q
      · rw [Fintype.sum_eq_single (⟨k, hk⟩ : ↥Q)]
        · simp [hk]
        · intro j hj
          have : k ≠ (j : Fin d) := by
            intro h
            exact hj (Subtype.ext h.symm)
          simp [this]
      · rw [dif_neg hk]
        refine Finset.sum_eq_zero fun j _ => ?_
        have : k ≠ (j : Fin d) := by
          intro h
          exact hk (h ▸ j.2)
        simp [this]
    -- Parseval
    have hnorm : ‖x‖ ^ 2 = ∑ k, (if h : k ∈ Q then ‖f ⟨k, h⟩‖ ^ 2 else 0) := by
      rw [← OrthonormalBasis.sum_sq_norm_inner_right hAE.eigenvectorBasis x]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hcoord k]
      split <;> simp
    have hQAE : qform (A + E) x
        = ∑ k, hAE.eigenvalues k * (if h : k ∈ Q then ‖f ⟨k, h⟩‖ ^ 2 else 0) := by
      rw [qform_eq_sum hAE]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hcoord k]
      congr 1
      split <;> simp
    -- strict lower bound for the perturbed form on the span of the high eigenvectors
    obtain ⟨j₀, hj₀⟩ : ∃ j : ↥Q, f j ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hfne (funext fun j => hcon j)
    have hstrict : θ * ‖x‖ ^ 2 < qform (A + E) x := by
      rw [hnorm, hQAE, Finset.mul_sum]
      refine Finset.sum_lt_sum (fun k _ => ?_) ⟨(j₀ : Fin d), Finset.mem_univ _, ?_⟩
      · by_cases hk : k ∈ Q
        · rw [dif_pos hk]
          have hkq : θ < hAE.eigenvalues k := by
            simpa [hQ] using hk
          exact mul_le_mul_of_nonneg_right hkq.le (by positivity)
        · simp [hk]
      · have hmem : (j₀ : Fin d) ∈ Q := j₀.2
        rw [dif_pos hmem]
        have hkq : θ < hAE.eigenvalues (j₀ : Fin d) := by simpa [hQ] using hmem
        have hpos : 0 < ‖f ⟨(j₀ : Fin d), hmem⟩‖ ^ 2 := by
          have : f ⟨(j₀ : Fin d), hmem⟩ ≠ 0 := by
            simpa using hj₀
          positivity
        exact (mul_lt_mul_of_pos_right hkq hpos)
    -- the unperturbed form is nonpositive on this vector
    have hAnonpos : qform A x ≤ 0 := by
      rw [qform_eq_sum hA]
      refine Finset.sum_nonpos fun i _ => ?_
      by_cases hi : i ∈ P
      · have : (inner ℂ (hA.eigenvectorBasis i) x : ℂ) = 0 := by
          have := congrFun hf ⟨i, hi⟩
          simpa [hR, hS, hx] using this
        simp [this]
      · have hle : hA.eigenvalues i ≤ 0 := by
          simp only [hP, Set.mem_toFinset, Set.mem_setOf_eq, not_lt] at hi
          exact hi
        exact mul_nonpos_of_nonpos_of_nonneg hle (by positivity)
    have hEbound : qform E x ≤ θ * ‖x‖ ^ 2 := qform_le_of_eigenvalues_le hE hEle x
    have := qform_add A E x
    linarith [hstrict, hAnonpos, hEbound, this]
  have hcard := LinearMap.finrank_le_finrank_of_injective (f := R ∘ₗ S) hinj
  rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
    Fintype.card_coe, Fintype.card_coe] at hcard
  rw [posIndex, posIndexAbove, posIndexAbove, ← hQ, ← hP]
  exact hcard

/-- Sanity check: all eigenvalues of the identity matrix equal `1`. -/
lemma eigenvalues_one (h1 : (1 : Matrix (Fin d) (Fin d) ℂ).IsHermitian) (i : Fin d) :
    h1.eigenvalues i = 1 := by
  have hmem := h1.eigenvalues_mem_spectrum_real i
  by_contra hne
  rw [spectrum.mem_iff] at hmem
  apply hmem
  have hx : (algebraMap ℝ (Matrix (Fin d) (Fin d) ℂ)) (h1.eigenvalues i) - 1
      = ((h1.eigenvalues i : ℂ) - 1) • (1 : Matrix (Fin d) (Fin d) ℂ) := by
    simp [Algebra.algebraMap_eq_smul_one, sub_smul, Complex.coe_smul]
  rw [hx, Matrix.isUnit_iff_isUnit_det]
  simp
  intro h
  have : (h1.eigenvalues i : ℝ) - 1 = 0 := by exact_mod_cast h
  exact absurd (by linarith : h1.eigenvalues i = 1) hne

/-- Sanity check: the identity matrix has `d` strictly positive eigenvalues, so the
counting functions above are not degenerate. -/
lemma posIndex_one (h1 : (1 : Matrix (Fin d) (Fin d) ℂ).IsHermitian) : posIndex h1 = d := by
  have hset : {i : Fin d | (0:ℝ) < h1.eigenvalues i} = Set.univ := by
    ext i
    simp [eigenvalues_one h1 i]
  simp [posIndex, posIndexAbove, hset]

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

