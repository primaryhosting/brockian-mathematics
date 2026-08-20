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
noncomputable def posIndex {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian) : ℕ :=
  #{i | 0 < hA.eigenvalues i}

/-- The number of eigenvalues of a Hermitian matrix that are strictly above `θ`. -/
noncomputable def posIndexAbove {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian) (θ : ℝ) : ℕ :=
  #{i | θ < hA.eigenvalues i}

/-- The quadratic form `x ↦ re ⟪x, M x⟫` associated with a matrix. -/
noncomputable def qform (M : Matrix (Fin d) (Fin d) ℂ) (x : EuclideanSpace ℂ (Fin d)) : ℝ :=
  (inner ℂ x (Matrix.toLpLin 2 2 M x)).re

lemma qform_add (M N : Matrix (Fin d) (Fin d) ℂ) (x : EuclideanSpace ℂ (Fin d)) :
    qform (M + N) x = qform M x + qform N x := by
  simp [qform, Complex.add_re]

lemma toLpLin_eigenvectorBasis {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian) (j : Fin d) :
    Matrix.toLpLin 2 2 A (hA.eigenvectorBasis j)
      = (hA.eigenvalues j : ℂ) • hA.eigenvectorBasis j := by
  ext k
  simp [Matrix.toLpLin_apply, hA.mulVec_eigenvectorBasis j, Complex.real_smul]

lemma repr_toLpLin {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian)
    (x : EuclideanSpace ℂ (Fin d)) (i : Fin d) :
    (hA.eigenvectorBasis.repr (Matrix.toLpLin 2 2 A x)).ofLp i
      = (hA.eigenvalues i : ℂ) * (hA.eigenvectorBasis.repr x).ofLp i := by
  have hsym := Matrix.isHermitian_iff_isSymmetric.mp hA
  rw [OrthonormalBasis.repr_apply_apply, ← hsym, toLpLin_eigenvectorBasis hA i,
    inner_smul_left, OrthonormalBasis.repr_apply_apply]
  simp

/-- Expansion of the quadratic form in the eigenbasis. -/
lemma qform_eq_sum {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian)
    (x : EuclideanSpace ℂ (Fin d)) :
    qform A x = ∑ i, hA.eigenvalues i * ‖(hA.eigenvectorBasis.repr x).ofLp i‖ ^ 2 := by
  have h : (inner ℂ x (Matrix.toLpLin 2 2 A x) : ℂ)
      = ∑ i, ((hA.eigenvalues i * ‖(hA.eigenvectorBasis.repr x).ofLp i‖ ^ 2 : ℝ) : ℂ) := by
    rw [← hA.eigenvectorBasis.repr.inner_map_map x (Matrix.toLpLin 2 2 A x), PiLp.inner_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [repr_toLpLin hA x i, RCLike.inner_apply]
    have hmul : (hA.eigenvalues i : ℂ) * (hA.eigenvectorBasis.repr x).ofLp i
          * (starRingEnd ℂ) ((hA.eigenvectorBasis.repr x).ofLp i)
        = (hA.eigenvalues i : ℂ) * ((hA.eigenvectorBasis.repr x).ofLp i
          * (starRingEnd ℂ) ((hA.eigenvectorBasis.repr x).ofLp i)) := by ring
    rw [hmul, Complex.mul_conj']
    push_cast
    ring
  rw [qform, h, Complex.re_sum]
  simp only [Complex.ofReal_re]

lemma norm_sq_eq_sum {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian)
    (x : EuclideanSpace ℂ (Fin d)) :
    ‖x‖ ^ 2 = ∑ i, ‖(hA.eigenvectorBasis.repr x).ofLp i‖ ^ 2 := by
  rw [← hA.eigenvectorBasis.repr.norm_map x, EuclideanSpace.norm_eq,
    Real.sq_sqrt (by positivity)]

/-- If all eigenvalues are `≤ θ`, the quadratic form is bounded by `θ ‖x‖²`. -/
lemma qform_le_of_eigenvalues_le {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian) {θ : ℝ}
    (h : ∀ i, hA.eigenvalues i ≤ θ) (x : EuclideanSpace ℂ (Fin d)) :
    qform A x ≤ θ * ‖x‖ ^ 2 := by
  rw [qform_eq_sum hA x, norm_sq_eq_sum hA x, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  exact mul_le_mul_of_nonneg_right (h i) (by positivity)

/-- If `x` has no component along eigenvectors with positive eigenvalue, `qform A x ≤ 0`. -/
lemma qform_nonpos_of_repr_eq_zero {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian)
    (x : EuclideanSpace ℂ (Fin d))
    (hx : ∀ i, 0 < hA.eigenvalues i → (hA.eigenvectorBasis.repr x).ofLp i = 0) :
    qform A x ≤ 0 := by
  rw [qform_eq_sum hA x]
  refine Finset.sum_nonpos fun i _ => ?_
  rcases le_or_gt (hA.eigenvalues i) 0 with hi | hi
  · exact mul_nonpos_of_nonpos_of_nonneg hi (by positivity)
  · simp [hx i hi]

/-- If `x` is supported on eigenvectors with eigenvalue `> θ` and `x ≠ 0`, then the quadratic
form is strictly bigger than `θ ‖x‖²`. -/
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
noncomputable def vecOf (b : OrthonormalBasis (Fin d) ℂ (EuclideanSpace ℂ (Fin d)))
    (S : Finset (Fin d)) : (S → ℂ) →ₗ[ℂ] EuclideanSpace ℂ (Fin d) where
  toFun c := b.repr.symm (WithLp.toLp 2 (fun k => if h : k ∈ S then c ⟨k, h⟩ else 0))
  map_add' c c' := by
    simp only [← map_add]
    congr 1
    ext k
    by_cases h : k ∈ S <;> simp [h]
  map_smul' a c := by
    simp only [← map_smul]
    congr 1
    ext k
    by_cases h : k ∈ S <;> simp [h]

lemma repr_vecOf (b : OrthonormalBasis (Fin d) ℂ (EuclideanSpace ℂ (Fin d)))
    (S : Finset (Fin d)) (c : S → ℂ) (k : Fin d) :
    (b.repr (vecOf b S c)).ofLp k = if h : k ∈ S then c ⟨k, h⟩ else 0 := by
  simp [vecOf]

lemma vecOf_eq_zero_iff (b : OrthonormalBasis (Fin d) ℂ (EuclideanSpace ℂ (Fin d)))
    (S : Finset (Fin d)) (c : S → ℂ) : vecOf b S c = 0 ↔ c = 0 := by
  constructor
  · intro h
    funext i
    have := repr_vecOf b S c i
    rw [h] at this
    simpa [i.2] using this.symm
  · rintro rfl
    simp only [vecOf, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, dite_eq_ite, ite_self]
    rw [show (WithLp.toLp 2 (fun _ : Fin d => (0 : ℂ))) = 0 from rfl, map_zero]

/-- **Weyl monotonicity** for the counting functions: if all eigenvalues of the Hermitian
perturbation `E` are bounded in absolute value by `θ`, then the number of eigenvalues of
`A + E` above `θ` is at most the number of positive eigenvalues of `A`. -/
theorem weyl_posIndexAbove {A E : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian)
    (hE : E.IsHermitian) (θ : ℝ) (hbd : ∀ i, |hE.eigenvalues i| ≤ θ) :
    posIndexAbove (hA.add hE) θ ≤ posIndex hA := by
  classical
  have hAE : (A + E).IsHermitian := hA.add hE
  set S : Finset (Fin d) := {i | θ < hAE.eigenvalues i} with hSdef
  set P : Finset (Fin d) := {i | 0 < hA.eigenvalues i} with hPdef
  let F : (S → ℂ) →ₗ[ℂ] (P → ℂ) :=
    { toFun := fun c j => (hA.eigenvectorBasis.repr (vecOf hAE.eigenvectorBasis S c)).ofLp j
      map_add' := by intro c c'; funext j; simp
      map_smul' := by intro a c; funext j; simp }
  have hinj : Function.Injective F := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    by_contra hcne
    set x : EuclideanSpace ℂ (Fin d) := vecOf hAE.eigenvectorBasis S c with hxdef
    have hx0 : x ≠ 0 := fun h => hcne ((vecOf_eq_zero_iff _ _ _).mp h)
    have h1 : θ * ‖x‖ ^ 2 < qform (A + E) x := by
      refine qform_gt_of_repr_eq_zero hAE x hx0 (fun i hi => ?_)
      by_contra hnot
      exact hi (by rw [hxdef, repr_vecOf]; simp [hSdef, hnot])
    have h2 : qform E x ≤ θ * ‖x‖ ^ 2 :=
      qform_le_of_eigenvalues_le hE (fun i => (abs_le.mp (hbd i)).2) x
    have h3 : qform A x ≤ 0 := by
      refine qform_nonpos_of_repr_eq_zero hA x (fun i hipos => ?_)
      have hiP : i ∈ P := by simp [hPdef, hipos]
      have := congrFun hc ⟨i, hiP⟩
      simpa [F] using this
    have h4 := qform_add A E x
    linarith
  have hcard := LinearMap.finrank_le_finrank_of_injective hinj
  simpa [Module.finrank_fintype_fun_eq_card, Fintype.card_subtype, posIndex, posIndexAbove,
    hSdef, hPdef] using hcard

end Zeta23Redux.LinAlg

