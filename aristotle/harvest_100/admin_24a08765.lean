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
noncomputable def posIndex {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian) : ℕ :=
  (Finset.univ.filter fun i => 0 < hA.eigenvalues i).card

/-- The number of eigenvalues of a Hermitian matrix that are strictly above `θ`. -/
noncomputable def posIndexAbove {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian) (θ : ℝ) : ℕ :=
  (Finset.univ.filter fun i => θ < hA.eigenvalues i).card

/-- The (real) quadratic form associated to a matrix, `x ↦ re ⟪x, A x⟫`. -/
noncomputable def qform (A : Matrix (Fin d) (Fin d) ℂ) (x : EuclideanSpace ℂ (Fin d)) : ℝ :=
  RCLike.re (inner ℂ x (Matrix.toEuclideanLin A x))

lemma toEuclideanLin_eigenvectorBasis {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian)
    (j : Fin d) :
    Matrix.toEuclideanLin A (hA.eigenvectorBasis j)
      = (hA.eigenvalues j : ℂ) • hA.eigenvectorBasis j := by
  have h := hA.mulVec_eigenvectorBasis j
  ext i
  simp [Matrix.toEuclideanLin, Matrix.toLpLin]
  rw [h]
  simp [RCLike.real_smul_eq_coe_smul (K := ℂ)]

/-- Expansion of the quadratic form in the eigenbasis. -/
lemma qform_eq {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian)
    (x : EuclideanSpace ℂ (Fin d)) :
    qform A x = ∑ i, hA.eigenvalues i * ‖inner ℂ (hA.eigenvectorBasis i) x‖ ^ 2 := by
  have key : ∀ a b : ℝ, (a : ℂ) * (b : ℂ) = ((a * b : ℝ) : ℂ) := by
    intro a b; push_cast; ring
  have hsym := Matrix.isHermitian_iff_isSymmetric.1 hA
  have h := hA.eigenvectorBasis.sum_inner_mul_inner x (Matrix.toEuclideanLin A x)
  have h2 : ∀ i : Fin d,
      inner ℂ x (hA.eigenvectorBasis i) * inner ℂ (hA.eigenvectorBasis i)
        (Matrix.toEuclideanLin A x)
      = ((hA.eigenvalues i * ‖inner ℂ (hA.eigenvectorBasis i) x‖ ^ 2 : ℝ) : ℂ) := by
    intro i
    have h3 : inner ℂ (hA.eigenvectorBasis i) (Matrix.toEuclideanLin A x)
        = (hA.eigenvalues i : ℂ) * inner ℂ (hA.eigenvectorBasis i) x := by
      rw [← hsym (hA.eigenvectorBasis i) x, toEuclideanLin_eigenvectorBasis hA i,
        inner_smul_left]
      simp
    have hc : inner ℂ x (hA.eigenvectorBasis i)
        = (starRingEnd ℂ) (inner ℂ (hA.eigenvectorBasis i) x) :=
      (inner_conj_symm _ _).symm
    rw [h3, hc, ← mul_assoc, mul_comm ((starRingEnd ℂ) _) _, mul_assoc, RCLike.conj_mul,
      ← RCLike.ofReal_pow]
    exact key _ _
  rw [Finset.sum_congr rfl (fun i _ => h2 i)] at h
  have h4 := congrArg RCLike.re h
  simp only [map_sum] at h4
  rw [qform, ← h4]
  exact Finset.sum_congr rfl fun i _ => rfl

/-- Parseval's identity in the eigenbasis. -/
lemma norm_sq_eq_sum {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian)
    (x : EuclideanSpace ℂ (Fin d)) :
    ‖x‖ ^ 2 = ∑ i, ‖inner ℂ (hA.eigenvectorBasis i) x‖ ^ 2 := by
  have h := hA.eigenvectorBasis.sum_inner_mul_inner x x
  have h2 : ∀ i : Fin d, inner ℂ x (hA.eigenvectorBasis i) * inner ℂ (hA.eigenvectorBasis i) x
      = ((‖inner ℂ (hA.eigenvectorBasis i) x‖ ^ 2 : ℝ) : ℂ) := by
    intro i
    have hc : inner ℂ x (hA.eigenvectorBasis i)
        = (starRingEnd ℂ) (inner ℂ (hA.eigenvectorBasis i) x) :=
      (inner_conj_symm _ _).symm
    rw [hc, RCLike.conj_mul]
    norm_cast
  rw [Finset.sum_congr rfl (fun i _ => h2 i)] at h
  have h3 := congrArg RCLike.re h
  simp only [map_sum, inner_self_eq_norm_sq] at h3
  exact h3.symm

lemma qform_add (A B : Matrix (Fin d) (Fin d) ℂ) (x : EuclideanSpace ℂ (Fin d)) :
    qform (A + B) x = qform A x + qform B x := by
  simp [qform]

lemma qform_le_of_eigenvalues_le {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian) {c : ℝ}
    (hc : ∀ i, hA.eigenvalues i ≤ c) (x : EuclideanSpace ℂ (Fin d)) :
    qform A x ≤ c * ‖x‖ ^ 2 := by
  rw [qform_eq hA, norm_sq_eq_sum hA, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hc i) (sq_nonneg _)

/-- Coefficients of a vector in the span of part of an orthonormal basis vanish elsewhere. -/
lemma inner_eq_zero_of_mem_span {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ
    (EuclideanSpace ℂ (Fin d))) (s : Finset ι) {x : EuclideanSpace ℂ (Fin d)}
    (hx : x ∈ Submodule.span ℂ (b '' (s : Set ι))) {i : ι} (hi : i ∉ s) :
    inner ℂ (b i) x = 0 := by
  have hle : Submodule.span ℂ (b '' (s : Set ι)) ≤
      LinearMap.ker (innerSL ℂ (b i) : EuclideanSpace ℂ (Fin d) →L[ℂ] ℂ).toLinearMap := by
    rw [Submodule.span_le]
    rintro _ ⟨j, hj, rfl⟩
    have hne : i ≠ j := by rintro rfl; exact hi hj
    simpa using b.orthonormal.2 hne
  simpa using hle hx

/-- On the span of eigenvectors with eigenvalues above `θ`, the quadratic form dominates
`θ ‖x‖²` strictly. -/
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
lemma qform_nonpos_of_coeffs {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian)
    {x : EuclideanSpace ℂ (Fin d)}
    (hx : ∀ i, 0 < hA.eigenvalues i → inner ℂ (hA.eigenvectorBasis i) x = 0) :
    qform A x ≤ 0 := by
  rw [qform_eq hA]
  refine Finset.sum_nonpos fun i _ => ?_
  rcases lt_or_ge 0 (hA.eigenvalues i) with hpos | hle
  · simp [hx i hpos]
  · exact mul_nonpos_of_nonpos_of_nonneg hle (sq_nonneg _)

/-- **Weyl monotonicity**: if every eigenvalue of the Hermitian perturbation `E` has absolute
value at most `θ`, then the number of eigenvalues of `A + E` strictly above `θ` is at most the
number of strictly positive eigenvalues of `A`. -/
theorem weyl_posIndexAbove {A E : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian)
    (hE : E.IsHermitian) (θ : ℝ) (hθ : ∀ i, |hE.eigenvalues i| ≤ θ) :
    posIndexAbove (hA.add hE) θ ≤ posIndex hA := by
  classical
  set hAE : (A + E).IsHermitian := hA.add hE
  set b := hAE.eigenvectorBasis
  set s : Finset (Fin d) := Finset.univ.filter fun i => θ < hAE.eigenvalues i with hsdef
  set t : Finset (Fin d) := Finset.univ.filter fun i => 0 < hA.eigenvalues i with htdef
  set S : Submodule ℂ (EuclideanSpace ℂ (Fin d)) := Submodule.span ℂ (b '' (s : Set (Fin d)))
    with hS
  -- the dimension of `S` is the number of eigenvalues above `θ`
  have hli : LinearIndependent ℂ (fun i : (s : Set (Fin d)) => b (i : Fin d)) := by
    have h1 : LinearIndependent ℂ (b : Fin d → EuclideanSpace ℂ (Fin d)) := by
      simpa using b.toBasis.linearIndependent
    exact h1.comp _ Subtype.val_injective
  have hdimS : Module.finrank ℂ S = s.card := by
    have hrange : Set.range (fun i : (s : Set (Fin d)) => b (i : Fin d))
        = b '' (s : Set (Fin d)) := (Set.image_eq_range _ _).symm
    have := finrank_span_eq_card hli
    rw [hrange] at this
    rw [hS, this]
    simp
  -- the linear map recording the coefficients along positive eigenvectors of `A`
  set co : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] ({i : Fin d // i ∈ t} → ℂ) :=
    LinearMap.pi fun i : {i : Fin d // i ∈ t} =>
      (innerSL ℂ (hA.eigenvectorBasis (i : Fin d)) :
        EuclideanSpace ℂ (Fin d) →L[ℂ] ℂ).toLinearMap with hco
  have hinj : Function.Injective (co.domRestrict S) := by
    rw [injective_iff_map_eq_zero]
    intro x hxz
    by_contra hne
    have hx0 : (x : EuclideanSpace ℂ (Fin d)) ≠ 0 := by
      intro h
      exact hne (Subtype.ext h)
    -- all coefficients along positive eigenvectors of `A` vanish
    have hcoeff : ∀ i, 0 < hA.eigenvalues i →
        inner ℂ (hA.eigenvectorBasis i) (x : EuclideanSpace ℂ (Fin d)) = 0 := by
      intro i hi
      have hit : i ∈ t := by simp [htdef, hi]
      have := congrFun hxz (⟨i, hit⟩ : {i : Fin d // i ∈ t})
      simpa [hco, LinearMap.domRestrict] using this
    have hqA : qform A (x : EuclideanSpace ℂ (Fin d)) ≤ 0 := qform_nonpos_of_coeffs hA hcoeff
    -- but on `S` the quadratic form of `A` is strictly positive
    have hmem : (x : EuclideanSpace ℂ (Fin d)) ∈ S := x.2
    have hs' : ∀ i ∈ s, θ < hAE.eigenvalues i := by
      intro i hi
      simpa [hsdef] using hi
    have h1 : θ * ‖(x : EuclideanSpace ℂ (Fin d))‖ ^ 2
        < qform (A + E) (x : EuclideanSpace ℂ (Fin d)) :=
      qform_gt_of_mem_span hAE hs' hmem hx0
    have h2 : qform E (x : EuclideanSpace ℂ (Fin d)) ≤ θ * ‖(x : EuclideanSpace ℂ (Fin d))‖ ^ 2 :=
      qform_le_of_eigenvalues_le hE (fun i => (le_abs_self _).trans (hθ i)) _
    have h3 := qform_add A E (x : EuclideanSpace ℂ (Fin d))
    linarith
  have hcard : Module.finrank ℂ S ≤ Module.finrank ℂ ({i : Fin d // i ∈ t} → ℂ) :=
    LinearMap.finrank_le_finrank_of_injective hinj
  have hfin : Module.finrank ℂ ({i : Fin d // i ∈ t} → ℂ) = t.card := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
  rw [posIndexAbove, posIndex, ← hsdef, ← htdef, ← hdimS, ← hfin]
  exact hcard

end Zeta23Redux.LinAlg

