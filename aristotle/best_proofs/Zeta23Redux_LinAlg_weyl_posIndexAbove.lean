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
noncomputable def qform (M : Matrix (Fin d) (Fin d) ℂ) (x : EuclideanSpace ℂ (Fin d)) : ℝ :=
  RCLike.re (inner ℂ x (Matrix.toEuclideanLin M x))

/-- The number of strictly positive eigenvalues of a Hermitian matrix. -/
noncomputable def posIndex {M : Matrix (Fin d) (Fin d) ℂ} (hM : M.IsHermitian) : ℕ :=
  (Finset.univ.filter fun i => 0 < hM.eigenvalues i).card

/-- The number of eigenvalues of a Hermitian matrix that are strictly above `theta`. -/
noncomputable def posIndexAbove {M : Matrix (Fin d) (Fin d) ℂ} (hM : M.IsHermitian)
    (theta : ℝ) : ℕ :=
  (Finset.univ.filter fun i => theta < hM.eigenvalues i).card

/-- Additivity of the quadratic form in the matrix. -/
lemma qform_add (M N : Matrix (Fin d) (Fin d) ℂ) (x : EuclideanSpace ℂ (Fin d)) :
    qform (M + N) x = qform M x + qform N x := by
  simp [qform, map_add]

/-- Real part of `conj z * (μ * z)` for real `μ`. -/
lemma re_conj_mul_smul (mu : ℝ) (z : ℂ) :
    RCLike.re ((starRingEnd ℂ) z * ((mu : ℂ) * z)) = mu * ‖z‖ ^ 2 := by
  rw [show (starRingEnd ℂ) z * ((mu : ℂ) * z) = (mu : ℂ) * (z * (starRingEnd ℂ) z) by ring,
    Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_mul]
  exact Complex.ofReal_re _

/-- The eigenvector basis diagonalizes the associated linear map. -/
lemma toEuclideanLin_eigenvectorBasis {M : Matrix (Fin d) (Fin d) ℂ} (hM : M.IsHermitian)
    (i : Fin d) :
    Matrix.toEuclideanLin M (hM.eigenvectorBasis i)
      = (hM.eigenvalues i : ℂ) • hM.eigenvectorBasis i := by
  have h := hM.mulVec_eigenvectorBasis i
  ext j
  simp [Matrix.toEuclideanLin, h]

/-- Expansion of the quadratic form in the eigenbasis. -/
lemma qform_eq_sum {M : Matrix (Fin d) (Fin d) ℂ} (hM : M.IsHermitian)
    (x : EuclideanSpace ℂ (Fin d)) :
    qform M x = ∑ i, hM.eigenvalues i * ‖(inner ℂ (hM.eigenvectorBasis i) x : ℂ)‖ ^ 2 := by
  have hsym : (Matrix.toEuclideanLin M).IsSymmetric := isHermitian_iff_isSymmetric.1 hM
  rw [qform, ← hM.eigenvectorBasis.sum_inner_mul_inner x (Matrix.toEuclideanLin M x), map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hsym (hM.eigenvectorBasis i) x, toEuclideanLin_eigenvectorBasis hM i, inner_smul_left,
    show (inner ℂ x (hM.eigenvectorBasis i) : ℂ)
      = starRingEnd ℂ (inner ℂ (hM.eigenvectorBasis i) x) from (inner_conj_symm _ _).symm,
    show (starRingEnd ℂ) ((hM.eigenvalues i : ℂ)) = (hM.eigenvalues i : ℂ) by simp]
  exact re_conj_mul_smul _ _

/-- Parseval's identity for an orthonormal basis. -/
lemma norm_sq_eq_sum (b : OrthonormalBasis (Fin d) ℂ (EuclideanSpace ℂ (Fin d)))
    (x : EuclideanSpace ℂ (Fin d)) :
    ‖x‖ ^ 2 = ∑ i, ‖(inner ℂ (b i) x : ℂ)‖ ^ 2 := by
  have h1 := congrArg RCLike.re (b.sum_inner_mul_inner x x)
  rw [inner_self_eq_norm_sq_to_K, map_sum,
    show RCLike.re ((RCLike.ofReal ‖x‖ : ℂ) ^ 2) = ‖x‖ ^ 2 by norm_cast] at h1
  rw [← h1]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show (inner ℂ x (b i) : ℂ) = starRingEnd ℂ (inner ℂ (b i) x) from (inner_conj_symm _ _).symm,
    RCLike.conj_mul]
  norm_cast

/-- If all eigenvalues are `≤ theta`, the quadratic form is bounded by `theta * ‖x‖²`. -/
lemma qform_le_of_eigenvalues_le {M : Matrix (Fin d) (Fin d) ℂ} (hM : M.IsHermitian)
    {theta : ℝ} (h : ∀ i, hM.eigenvalues i ≤ theta) (x : EuclideanSpace ℂ (Fin d)) :
    qform M x ≤ theta * ‖x‖ ^ 2 := by
  rw [qform_eq_sum hM, norm_sq_eq_sum hM.eigenvectorBasis x, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  exact mul_le_mul_of_nonneg_right (h i) (by positivity)

/-- Coefficients outside `s` vanish for a vector in the span of the eigenvectors indexed by `s`. -/
lemma inner_eq_zero_of_mem_span {M : Matrix (Fin d) (Fin d) ℂ} (hM : M.IsHermitian)
    {s : Finset (Fin d)} {x : EuclideanSpace ℂ (Fin d)}
    (hx : x ∈ Submodule.span ℂ (hM.eigenvectorBasis '' (s : Set (Fin d)))) {i : Fin d}
    (hi : i ∉ s) : (inner ℂ (hM.eigenvectorBasis i) x : ℂ) = 0 := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨j, hj, rfl⟩ := hy
      have hij : i ≠ j := fun h => hi (h ▸ hj)
      exact hM.eigenvectorBasis.orthonormal.2 hij
  | zero => simp
  | add y z _ _ hy hz => rw [inner_add_right, hy, hz, add_zero]
  | smul c y _ hy => rw [inner_smul_right, hy, mul_zero]

/-- On the span of eigenvectors with eigenvalue `> theta`, the form is `> theta * ‖x‖²`
(for `x ≠ 0`). -/
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
lemma qform_nonpos_of_mem_span {M : Matrix (Fin d) (Fin d) ℂ} (hM : M.IsHermitian)
    {x : EuclideanSpace ℂ (Fin d)}
    (hx : x ∈ Submodule.span ℂ
      (hM.eigenvectorBasis '' ((Finset.univ.filter fun i => hM.eigenvalues i ≤ 0) :
        Set (Fin d)))) :
    qform M x ≤ 0 := by
  classical
  set s : Finset (Fin d) := Finset.univ.filter fun i => hM.eigenvalues i ≤ 0 with hs
  rw [qform_eq_sum hM]
  refine Finset.sum_nonpos fun i _ => ?_
  by_cases hi : i ∈ s
  · have h1 : hM.eigenvalues i ≤ 0 := by rw [hs] at hi; simpa using hi
    exact mul_nonpos_of_nonpos_of_nonneg h1 (by positivity)
  · rw [inner_eq_zero_of_mem_span hM hx hi]
    simp

/-- The span of a set of eigenvectors has dimension equal to the number of indices. -/
lemma finrank_span_eigenvectors {M : Matrix (Fin d) (Fin d) ℂ} (hM : M.IsHermitian)
    (s : Finset (Fin d)) :
    Module.finrank ℂ
      (Submodule.span ℂ (hM.eigenvectorBasis '' (s : Set (Fin d)))) = s.card := by
  classical
  have hli : LinearIndependent ℂ fun i : (s : Set (Fin d)) => hM.eigenvectorBasis i := by
    have := hM.eigenvectorBasis.toBasis.linearIndependent
    simpa using this.comp (fun i : (s : Set (Fin d)) => (i : Fin d)) Subtype.val_injective
  have hrange : Set.range (fun i : (s : Set (Fin d)) => hM.eigenvectorBasis i)
      = hM.eigenvectorBasis '' (s : Set (Fin d)) := by
    ext y
    constructor
    · rintro ⟨⟨i, hi⟩, rfl⟩
      exact ⟨i, hi, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
  rw [← hrange, finrank_span_eq_card hli]
  simp

/-- **Weyl monotonicity**: if `A` and `E` are Hermitian and every eigenvalue of `E` has absolute
value at most `theta`, then the number of eigenvalues of `A + E` strictly above `theta` is at most
the number of strictly positive eigenvalues of `A`. -/
theorem weyl_posIndexAbove {d : ℕ} {A E : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.IsHermitian) (hE : E.IsHermitian) (theta : ℝ)
    (hEtheta : ∀ i, |hE.eigenvalues i| ≤ theta) :
    posIndexAbove (hA.add hE) theta ≤ posIndex hA := by
  classical
  set hAE : (A + E).IsHermitian := hA.add hE with hAEdef
  set sP : Finset (Fin d) := Finset.univ.filter fun i => theta < hAE.eigenvalues i with hsP
  set sN : Finset (Fin d) := Finset.univ.filter fun i => hA.eigenvalues i ≤ 0 with hsN
  set S : Submodule ℂ (EuclideanSpace ℂ (Fin d)) :=
    Submodule.span ℂ (hAE.eigenvectorBasis '' (sP : Set (Fin d))) with hS
  set T : Submodule ℂ (EuclideanSpace ℂ (Fin d)) :=
    Submodule.span ℂ (hA.eigenvectorBasis '' (sN : Set (Fin d))) with hT
  have hEle : ∀ i, hE.eigenvalues i ≤ theta := fun i => le_trans (le_abs_self _) (hEtheta i)
  have hinf : S ⊓ T = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxS, hxT⟩ := hx
    by_contra hne
    have hx0 : x ≠ 0 := by simpa using hne
    have h1 : theta * ‖x‖ ^ 2 < qform (A + E) x := qform_gt_of_mem_span hAE hxS hx0
    have h2 : qform A x ≤ 0 := qform_nonpos_of_mem_span hA hxT
    have h3 : qform E x ≤ theta * ‖x‖ ^ 2 := qform_le_of_eigenvalues_le hE hEle x
    rw [qform_add] at h1
    linarith
  have hdimS : Module.finrank ℂ S = sP.card := finrank_span_eigenvectors hAE sP
  have hdimT : Module.finrank ℂ T = sN.card := finrank_span_eigenvectors hA sN
  have hsum : Module.finrank ℂ (S ⊔ T : Submodule ℂ (EuclideanSpace ℂ (Fin d)))
      + Module.finrank ℂ (S ⊓ T : Submodule ℂ (EuclideanSpace ℂ (Fin d)))
      = Module.finrank ℂ S + Module.finrank ℂ T :=
    Submodule.finrank_sup_add_finrank_inf_eq S T
  have hle : Module.finrank ℂ (S ⊔ T : Submodule ℂ (EuclideanSpace ℂ (Fin d))) ≤ d := by
    have := Submodule.finrank_le (S ⊔ T)
    simpa [finrank_euclideanSpace] using this
  have hbot : Module.finrank ℂ (S ⊓ T : Submodule ℂ (EuclideanSpace ℂ (Fin d))) = 0 := by
    rw [hinf]
    simp
  have hcard : sN.card + (Finset.univ.filter fun i => 0 < hA.eigenvalues i).card = d := by
    have := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin d))) (p := fun i => hA.eigenvalues i ≤ 0)
    simp only [not_le] at this
    simpa [hsN] using this
  have hfin : sP.card + sN.card ≤ d := by omega
  simp only [posIndexAbove, posIndex, ← hsP]
  omega

end Zeta23Redux.LinAlg

