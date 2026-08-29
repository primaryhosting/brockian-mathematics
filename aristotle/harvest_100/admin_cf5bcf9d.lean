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

namespace Zeta23Redux.LinAlg

open Matrix Finset

variable {d : ℕ}

/-- The Rayleigh quadratic form of a matrix `M` at a vector `x` of Euclidean space:
`Re ⟪x, M x⟫`. -/
noncomputable def quadForm (M : Matrix (Fin d) (Fin d) ℂ) (x : EuclideanSpace ℂ (Fin d)) : ℝ :=
  (inner ℂ x (Matrix.toEuclideanLin M x)).re

/-- The number of strictly positive eigenvalues of a Hermitian matrix. -/
noncomputable def posIndex {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian) : ℕ :=
  #{i | 0 < hA.eigenvalues i}

/-- The number of eigenvalues of a Hermitian matrix that lie strictly above `θ`. -/
noncomputable def posIndexAbove {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian) (θ : ℝ) : ℕ :=
  #{i | θ < hA.eigenvalues i}

lemma posIndex_eq_posIndexAbove_zero {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian) :
    posIndex hA = posIndexAbove hA 0 := rfl

/-- The eigenvector basis diagonalizes the matrix, viewed as a linear map on Euclidean space. -/
lemma toEuclideanLin_eigenvectorBasis {M : Matrix (Fin d) (Fin d) ℂ} (hM : M.IsHermitian)
    (i : Fin d) :
    Matrix.toEuclideanLin M (hM.eigenvectorBasis i)
      = (hM.eigenvalues i : ℂ) • hM.eigenvectorBasis i := by
  apply WithLp.ofLp_injective (p := 2)
  simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply, hM.mulVec_eigenvectorBasis i]

/-- Expansion of the quadratic form in the eigenbasis. -/
lemma quadForm_eq_sum {M : Matrix (Fin d) (Fin d) ℂ} (hM : M.IsHermitian)
    (x : EuclideanSpace ℂ (Fin d)) :
    quadForm M x = ∑ i, hM.eigenvalues i * ‖(inner ℂ (hM.eigenvectorBasis i) x : ℂ)‖ ^ 2 := by
  have hsym : (Matrix.toEuclideanLin M).IsSymmetric := Matrix.isHermitian_iff_isSymmetric.1 hM
  have key : (inner ℂ x (Matrix.toEuclideanLin M x) : ℂ)
      = ∑ i, ((hM.eigenvalues i * ‖(inner ℂ (hM.eigenvectorBasis i) x : ℂ)‖ ^ 2 : ℝ) : ℂ) := by
    rw [← hM.eigenvectorBasis.sum_inner_mul_inner x (Matrix.toEuclideanLin M x)]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : (inner ℂ (hM.eigenvectorBasis i) (Matrix.toEuclideanLin M x) : ℂ)
        = (hM.eigenvalues i : ℂ) * inner ℂ (hM.eigenvectorBasis i) x := by
      rw [← hsym, toEuclideanLin_eigenvectorBasis hM i, inner_smul_left]
      simp
    rw [h1, ← inner_conj_symm (𝕜 := ℂ) x (hM.eigenvectorBasis i)]
    push_cast
    rw [show (starRingEnd ℂ) (inner ℂ (hM.eigenvectorBasis i) x)
          * ((hM.eigenvalues i : ℂ) * inner ℂ (hM.eigenvectorBasis i) x)
        = (hM.eigenvalues i : ℂ)
          * ((starRingEnd ℂ) (inner ℂ (hM.eigenvectorBasis i) x)
            * inner ℂ (hM.eigenvectorBasis i) x) by ring, Complex.conj_mul']
  rw [quadForm, key, ← Complex.ofReal_sum]
  simp only [Complex.ofReal_re]

/-- Squared norm expansion in the eigenbasis. -/
lemma norm_sq_eq_sum {M : Matrix (Fin d) (Fin d) ℂ} (hM : M.IsHermitian)
    (x : EuclideanSpace ℂ (Fin d)) :
    ‖x‖ ^ 2 = ∑ i, ‖(inner ℂ (hM.eigenvectorBasis i) x : ℂ)‖ ^ 2 :=
  (hM.eigenvectorBasis.sum_sq_norm_inner_right x).symm

/-- If all eigenvalues are at most `c`, the quadratic form is bounded by `c ‖x‖²`. -/
lemma quadForm_le {M : Matrix (Fin d) (Fin d) ℂ} (hM : M.IsHermitian) {c : ℝ}
    (h : ∀ i, hM.eigenvalues i ≤ c) (x : EuclideanSpace ℂ (Fin d)) :
    quadForm M x ≤ c * ‖x‖ ^ 2 := by
  rw [quadForm_eq_sum hM, norm_sq_eq_sum hM x, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_right (h i) (by positivity)

/-- Coefficients of a vector in the span of part of the eigenbasis vanish off that part. -/
lemma inner_eq_zero_of_mem_span {M : Matrix (Fin d) (Fin d) ℂ} (hM : M.IsHermitian)
    (s : Finset (Fin d)) {x : EuclideanSpace ℂ (Fin d)}
    (hx : x ∈ Submodule.span ℂ (Set.range fun j : (s : Set (Fin d)) => hM.eigenvectorBasis j))
    {i : Fin d} (hi : i ∉ s) : (inner ℂ (hM.eigenvectorBasis i) x : ℂ) = 0 := by
  have : x ∈ LinearMap.ker (innerSL ℂ (hM.eigenvectorBasis i)).toLinearMap := by
    refine Submodule.span_le.2 ?_ hx
    rintro y ⟨j, rfl⟩
    have hij : i ≠ (j : Fin d) := by
      rintro rfl
      exact hi j.2
    simp [SetLike.mem_coe, LinearMap.mem_ker,
      hM.eigenvectorBasis.orthonormal.2 hij]
  simpa using this

/-- On the span of eigenvectors with eigenvalues `≤ c`, the quadratic form is at most `c ‖x‖²`. -/
lemma quadForm_le_of_mem_span {M : Matrix (Fin d) (Fin d) ℂ} (hM : M.IsHermitian)
    (s : Finset (Fin d)) {c : ℝ} (hc : ∀ i ∈ s, hM.eigenvalues i ≤ c)
    {x : EuclideanSpace ℂ (Fin d)}
    (hx : x ∈ Submodule.span ℂ (Set.range fun j : (s : Set (Fin d)) => hM.eigenvectorBasis j)) :
    quadForm M x ≤ c * ‖x‖ ^ 2 := by
  have hzero : ∀ i ∉ s, (inner ℂ (hM.eigenvectorBasis i) x : ℂ) = 0 := fun i hi =>
    inner_eq_zero_of_mem_span hM s hx hi
  have h1 : quadForm M x = ∑ i ∈ s, hM.eigenvalues i * ‖(inner ℂ (hM.eigenvectorBasis i) x : ℂ)‖ ^ 2 := by
    rw [quadForm_eq_sum hM]
    refine (Finset.sum_subset (Finset.subset_univ s) ?_).symm
    intro i _ hi
    simp [hzero i hi]
  have h2 : ‖x‖ ^ 2 = ∑ i ∈ s, ‖(inner ℂ (hM.eigenvectorBasis i) x : ℂ)‖ ^ 2 := by
    rw [norm_sq_eq_sum hM x]
    refine (Finset.sum_subset (Finset.subset_univ s) ?_).symm
    intro i _ hi
    simp [hzero i hi]
  rw [h1, h2, Finset.mul_sum]
  exact Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_right (hc i hi) (by positivity)

/-- On the span of eigenvectors with eigenvalues `> c`, the quadratic form strictly exceeds
`c ‖x‖²` for nonzero `x`. -/
lemma lt_quadForm_of_mem_span {M : Matrix (Fin d) (Fin d) ℂ} (hM : M.IsHermitian)
    (s : Finset (Fin d)) {c : ℝ} (hc : ∀ i ∈ s, c < hM.eigenvalues i)
    {x : EuclideanSpace ℂ (Fin d)}
    (hx : x ∈ Submodule.span ℂ (Set.range fun j : (s : Set (Fin d)) => hM.eigenvectorBasis j))
    (hx0 : x ≠ 0) :
    c * ‖x‖ ^ 2 < quadForm M x := by
  have hzero : ∀ i ∉ s, (inner ℂ (hM.eigenvectorBasis i) x : ℂ) = 0 := fun i hi =>
    inner_eq_zero_of_mem_span hM s hx hi
  have h1 : quadForm M x = ∑ i ∈ s, hM.eigenvalues i * ‖(inner ℂ (hM.eigenvectorBasis i) x : ℂ)‖ ^ 2 := by
    rw [quadForm_eq_sum hM]
    refine (Finset.sum_subset (Finset.subset_univ s) ?_).symm
    intro i _ hi
    simp [hzero i hi]
  have h2 : ‖x‖ ^ 2 = ∑ i ∈ s, ‖(inner ℂ (hM.eigenvectorBasis i) x : ℂ)‖ ^ 2 := by
    rw [norm_sq_eq_sum hM x]
    refine (Finset.sum_subset (Finset.subset_univ s) ?_).symm
    intro i _ hi
    simp [hzero i hi]
  have hpos : 0 < ‖x‖ ^ 2 := by positivity
  have hex : ∃ i ∈ s, 0 < ‖(inner ℂ (hM.eigenvectorBasis i) x : ℂ)‖ ^ 2 := by
    by_contra hcon
    push_neg at hcon
    have : ‖x‖ ^ 2 = 0 := by
      rw [h2]
      refine Finset.sum_eq_zero fun i hi => ?_
      have := hcon i hi
      have h0 : (0:ℝ) ≤ ‖(inner ℂ (hM.eigenvectorBasis i) x : ℂ)‖ ^ 2 := by positivity
      linarith
    exact absurd this (ne_of_gt hpos)
  rw [h1, h2, Finset.mul_sum]
  refine Finset.sum_lt_sum (fun i hi => mul_le_mul_of_nonneg_right (le_of_lt (hc i hi))
    (by positivity)) ?_
  obtain ⟨i, hi, hip⟩ := hex
  exact ⟨i, hi, by nlinarith [hc i hi]⟩

/-- The dimension of the span of a subfamily of the eigenbasis. -/
lemma finrank_span_eigen {M : Matrix (Fin d) (Fin d) ℂ} (hM : M.IsHermitian)
    (s : Finset (Fin d)) :
    Module.finrank ℂ
        (Submodule.span ℂ (Set.range fun j : (s : Set (Fin d)) => hM.eigenvectorBasis j))
      = s.card := by
  have hli : LinearIndependent ℂ fun j : (s : Set (Fin d)) => hM.eigenvectorBasis (j : Fin d) :=
    (hM.eigenvectorBasis.toBasis.linearIndependent).comp _ Subtype.val_injective
  rw [finrank_span_eq_card hli]
  simp

/-- **Weyl monotonicity**: if every eigenvalue of the Hermitian perturbation `E` has absolute
value at most `θ`, then the number of eigenvalues of `A + E` strictly above `θ` is at most the
number of strictly positive eigenvalues of `A`. -/
theorem weyl_posIndexAbove {d : ℕ} {A E : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.IsHermitian) (hE : E.IsHermitian) (θ : ℝ)
    (hbd : ∀ i, |hE.eigenvalues i| ≤ θ) :
    posIndexAbove (hA.add hE) θ ≤ posIndex hA := by
  classical
  set hB : (A + E).IsHermitian := hA.add hE with hBdef
  set S : Finset (Fin d) := {i | θ < hB.eigenvalues i} with hS
  set T : Finset (Fin d) := {i | 0 < hA.eigenvalues i} with hT
  set V : Submodule ℂ (EuclideanSpace ℂ (Fin d)) :=
    Submodule.span ℂ (Set.range fun j : (S : Set (Fin d)) => hB.eigenvectorBasis j) with hV
  set W : Submodule ℂ (EuclideanSpace ℂ (Fin d)) :=
    Submodule.span ℂ (Set.range fun j : ((Tᶜ : Finset (Fin d)) : Set (Fin d)) =>
      hA.eigenvectorBasis j) with hW
  -- quadratic form additivity
  have hadd : ∀ x : EuclideanSpace ℂ (Fin d), quadForm (A + E) x = quadForm A x + quadForm E x := by
    intro x
    simp [quadForm, map_add]
  -- the two subspaces intersect trivially
  have hdisj : V ⊓ W = ⊥ := by
    refine (Submodule.eq_bot_iff _).2 ?_
    rintro x ⟨hxV, hxW⟩
    by_contra hx0
    have h1 : θ * ‖x‖ ^ 2 < quadForm (A + E) x :=
      lt_quadForm_of_mem_span hB S (fun i hi => by simpa [hS] using hi) hxV hx0
    have h2 : quadForm A x ≤ 0 * ‖x‖ ^ 2 := by
      refine quadForm_le_of_mem_span hA (Tᶜ) (fun i hi => ?_) hxW
      simp only [hT, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and,
        not_lt] at hi
      exact hi
    have h3 : quadForm E x ≤ θ * ‖x‖ ^ 2 :=
      quadForm_le hE (fun i => (abs_le.1 (hbd i)).2) x
    rw [hadd x] at h1
    simp only [zero_mul] at h2
    linarith
  -- dimension count
  have hdimV : Module.finrank ℂ V = S.card := finrank_span_eigen hB S
  have hdimW : Module.finrank ℂ W = (Tᶜ : Finset (Fin d)).card := finrank_span_eigen hA _
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq V W
  have hle : Module.finrank ℂ (V ⊔ W : Submodule ℂ (EuclideanSpace ℂ (Fin d)))
      ≤ Module.finrank ℂ (EuclideanSpace ℂ (Fin d)) := Submodule.finrank_le _
  rw [hdisj] at hsum
  simp only [finrank_bot, add_zero, hdimV, hdimW] at hsum
  have hd : Module.finrank ℂ (EuclideanSpace ℂ (Fin d)) = d := finrank_euclideanSpace_fin
  rw [hd] at hle
  have hcompl : (Tᶜ : Finset (Fin d)).card = d - T.card := by
    rw [Finset.card_compl]
    simp
  have hTle : T.card ≤ d := by
    simpa using (Finset.card_le_univ T)
  have : S.card + (d - T.card) ≤ d := by
    rw [← hcompl, ← hsum]; exact hle
  show S.card ≤ T.card
  omega

end Zeta23Redux.LinAlg

