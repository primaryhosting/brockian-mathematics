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

/-!
# Weyl Pos Index Above
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.weyl_posIndexAbove
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix
open scoped BigOperators

namespace Zeta23Redux.LinAlg

section Aux

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The (real part of the) Hermitian quadratic form `x ↦ x* M x`. -/
private noncomputable def qform (M : Matrix n n ℂ) (x : n → ℂ) : ℝ := (star x ⬝ᵥ M *ᵥ x).re

/-- The squared euclidean norm of a vector. -/
private noncomputable def nsq (x : n → ℂ) : ℝ := (star x ⬝ᵥ x).re

omit [DecidableEq n] in
private lemma nsq_eq_sum (x : n → ℂ) : nsq x = ∑ i, ‖x i‖ ^ 2 := by
  simp only [nsq, dotProduct, Pi.star_apply, RCLike.star_def, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Complex.mul_re, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]

omit [DecidableEq n] in
private lemma qform_add (A B : Matrix n n ℂ) (x : n → ℂ) :
    qform (A + B) x = qform A x + qform B x := by
  simp [qform, add_mulVec, dotProduct_add]

omit [DecidableEq n] in
private lemma star_mulVec_star (U : Matrix n n ℂ) (x : n → ℂ) :
    star (star U *ᵥ x) = star x ᵥ* U := by
  rw [star_mulVec, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]

/-- Diagonalisation of the quadratic form of a Hermitian matrix in its eigenbasis. -/
private lemma qform_eq_sum {M : Matrix n n ℂ} (hM : M.IsHermitian) (x : n → ℂ) :
    qform M x = ∑ i, hM.eigenvalues i *
      ‖(star (hM.eigenvectorUnitary : Matrix n n ℂ) *ᵥ x) i‖ ^ 2 := by
  set U : Matrix n n ℂ := (hM.eigenvectorUnitary : Matrix n n ℂ)
  set D : Matrix n n ℂ := diagonal (RCLike.ofReal ∘ hM.eigenvalues) with hD
  set y := star U *ᵥ x with hy
  have hspec : M = U * D * star U := by
    conv_lhs => rw [hM.spectral_theorem, Unitary.conjStarAlgAut_apply]
  have h1 : star x ⬝ᵥ M *ᵥ x = star y ⬝ᵥ (D *ᵥ y) := by
    conv_lhs => rw [hspec]
    rw [star_mulVec_star, hy]
    simp [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, Matrix.dotProduct_mulVec]
  rw [qform, h1, hD]
  simp only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply, RCLike.star_def,
    Function.comp_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Complex.mul_re, Complex.mul_im, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  ring

/-- Multiplying by a unitary matrix preserves the squared norm. -/
private lemma nsq_mulVec (U : Matrix.unitaryGroup n ℂ) (x : n → ℂ) :
    nsq ((U : Matrix n n ℂ) *ᵥ x) = nsq x := by
  have hst : star ((U : Matrix n n ℂ) *ᵥ x) = star x ᵥ* star (U : Matrix n n ℂ) := by
    rw [star_mulVec, Matrix.star_eq_conjTranspose]
  simp only [nsq, hst, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.UnitaryGroup.star_mul_self, Matrix.one_mulVec]

private lemma nsq_star_mulVec (U : Matrix.unitaryGroup n ℂ) (x : n → ℂ) :
    nsq (star (U : Matrix n n ℂ) *ᵥ x) = nsq x := by
  have hst : star (star (U : Matrix n n ℂ) *ᵥ x) = star x ᵥ* (U : Matrix n n ℂ) :=
    star_mulVec_star _ _
  have hUU : (U : Matrix n n ℂ) * star (U : Matrix n n ℂ) = 1 := by simp
  simp only [nsq, hst, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hUU, Matrix.one_mulVec]

/-- If all eigenvalues of a Hermitian matrix are at most `θ`, then `x* M x ≤ θ ‖x‖²`. -/
private lemma qform_le {M : Matrix n n ℂ} (hM : M.IsHermitian) {θ : ℝ}
    (hb : ∀ i, hM.eigenvalues i ≤ θ) (x : n → ℂ) : qform M x ≤ θ * nsq x := by
  rw [qform_eq_sum hM, ← nsq_star_mulVec hM.eigenvectorUnitary x, nsq_eq_sum,
    Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hb i) (by positivity)

end Aux

variable {d : ℕ}

/-- The number of eigenvalues of a Hermitian matrix that are strictly larger than `θ`. -/
noncomputable def posIndexAbove {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian) (θ : ℝ) : ℕ :=
  (Finset.univ.filter fun i => θ < hA.eigenvalues i).card

/-- The number of strictly positive eigenvalues of a Hermitian matrix. -/
noncomputable def posIndex {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian) : ℕ :=
  posIndexAbove hA 0

section Main

variable {A E : Matrix (Fin d) (Fin d) ℂ}

/-- Key step: a vector whose `(A+E)`-eigen-coordinates are supported on the eigenvalues above `θ`
and whose `A`-eigen-coordinates vanish on the positive eigenvalues of `A` must be zero. -/
private lemma key (hA : A.IsHermitian) (hE : E.IsHermitian) (θ : ℝ)
    (hEθ : ∀ i, |hE.eigenvalues i| ≤ θ) (c : Fin d → ℂ)
    (hsupp : ∀ i, c i ≠ 0 → θ < (hA.add hE).eigenvalues i)
    (hker : ∀ j, 0 < hA.eigenvalues j →
      (star ((hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)) *ᵥ
        ((hA.add hE).eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) *ᵥ c) j = 0) :
    c = 0 := by
  classical
  by_contra hc
  set V : Matrix (Fin d) (Fin d) ℂ :=
    ((hA.add hE).eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) with hV
  set x : Fin d → ℂ := V *ᵥ c with hx
  -- coordinates of `x` in the `(A+E)`-eigenbasis are `c`
  have hVc : star V *ᵥ x = c := by
    rw [hx, Matrix.mulVec_mulVec, hV, Matrix.UnitaryGroup.star_mul_self, Matrix.one_mulVec]
  have hnsqx : nsq x = nsq c := by
    rw [hx, hV, nsq_mulVec]
  -- `x* (A+E) x > θ ‖x‖²`
  have h1 : θ * nsq x < qform (A + E) x := by
    rw [qform_eq_sum (hA.add hE) x, hnsqx, nsq_eq_sum, Finset.mul_sum]
    have hcoord : (star ((hA.add hE).eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) *ᵥ x) = c :=
      hVc
    rw [hcoord]
    obtain ⟨i0, hi0⟩ : ∃ i, c i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hc (funext fun i => h i)
    refine Finset.sum_lt_sum (fun i _ => ?_) ⟨i0, Finset.mem_univ _, ?_⟩
    · rcases eq_or_ne (c i) 0 with h | h
      · simp [h]
      · exact mul_le_mul_of_nonneg_right (le_of_lt (hsupp i h)) (by positivity)
    · have hpos : 0 < ‖c i0‖ ^ 2 := by positivity
      exact mul_lt_mul_of_pos_right (hsupp i0 hi0) hpos
  -- `x* E x ≤ θ ‖x‖²`
  have h2 : qform E x ≤ θ * nsq x :=
    qform_le hE (fun i => (abs_le.mp (hEθ i)).2) x
  -- hence `x* A x > 0`
  have h3 : 0 < qform A x := by
    have := qform_add A E x
    linarith [h1, h2, this]
  -- but the `A`-coordinates of `x` vanish where the eigenvalues are positive, so `x* A x ≤ 0`
  have h4 : qform A x ≤ 0 := by
    rw [qform_eq_sum hA x]
    refine Finset.sum_nonpos fun j _ => ?_
    rcases lt_or_ge 0 (hA.eigenvalues j) with hj | hj
    · have h0 : (star ((hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)) *ᵥ x) j = 0 :=
        hker j hj
      rw [h0]
      simp
    · exact mul_nonpos_of_nonpos_of_nonneg hj (by positivity)
  linarith

/-- **Weyl monotonicity / eigenvalue interlacing bound.** If `A` and `E` are Hermitian complex
matrices and every eigenvalue of `E` has absolute value at most `θ`, then the number of
eigenvalues of `A + E` strictly above `θ` is at most the number of strictly positive
eigenvalues of `A`. -/
theorem weyl_posIndexAbove (hA : A.IsHermitian) (hE : E.IsHermitian) (θ : ℝ)
    (hEθ : ∀ i, |hE.eigenvalues i| ≤ θ) :
    posIndexAbove (hA.add hE) θ ≤ posIndex hA := by
  classical
  set P : Fin d → Prop := fun j => 0 < hA.eigenvalues j with hP
  set Q : Fin d → Prop := fun i => θ < (hA.add hE).eigenvalues i with hQ
  set W : Matrix (Fin d) (Fin d) ℂ :=
    star ((hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)) *
      ((hA.add hE).eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) with hW
  set M : Matrix {j // P j} {i // Q i} ℂ := W.submatrix Subtype.val Subtype.val with hM
  have hinj : Function.Injective (Matrix.mulVecLin M) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro cs hcs
    set c : Fin d → ℂ := fun i => if h : Q i then cs ⟨i, h⟩ else 0 with hc
    have hc0 : c = 0 := by
      refine key hA hE θ hEθ c ?_ ?_
      · intro i hi
        by_contra h
        exact hi (by rw [hc]; exact dif_neg (show ¬ Q i from h))
      · intro j hj
        have hexp : ∀ j : Fin d, (star ((hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)) *ᵥ
            ((hA.add hE).eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) *ᵥ c) j
            = (W *ᵥ c) j := by
          intro j
          rw [hW, ← Matrix.mulVec_mulVec]
        rw [hexp j]
        have hstep1 : (W *ᵥ c) j = ∑ x ∈ Finset.univ.filter Q, W j x * c x := by
          rw [Matrix.mulVec, dotProduct]
          refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
          intro i _ hi
          have hQi : ¬ Q i := by simpa using hi
          rw [hc]
          simp [dif_neg hQi]
        have hstep2 : ∑ x ∈ Finset.univ.filter Q, W j x * c x
            = ∑ i : {i // Q i}, W j (i : Fin d) * c (i : Fin d) :=
          Finset.sum_subtype _ (by simp) _
        have hstep3 : ∑ i : {i // Q i}, W j (i : Fin d) * c (i : Fin d)
            = ∑ i : {i // Q i}, W j (i : Fin d) * cs i := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hc]
          simp [dif_pos i.2]
        rw [hstep1, hstep2, hstep3]
        have hz := congrFun hcs ⟨j, hj⟩
        simpa [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, hM] using hz
    funext i
    have hi := congrFun hc0 (i : Fin d)
    rw [hc] at hi
    simpa [dif_pos i.2] using hi
  have hcard := LinearMap.finrank_le_finrank_of_injective (R := ℂ) hinj
  rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card] at hcard
  rw [posIndexAbove, posIndex, posIndexAbove]
  simpa [Fintype.card_subtype, hP, hQ] using hcard

end Main

/-- Sanity check: the identity matrix of size `d` has `d` strictly positive eigenvalues. -/
theorem posIndex_one : posIndex (Matrix.isHermitian_one (n := Fin d) (α := ℂ)) = d := by
  have h : ∀ i, (Matrix.isHermitian_one (n := Fin d) (α := ℂ)).eigenvalues i = 1 := by
    intro i
    have h1 := (Matrix.isHermitian_one (n := Fin d) (α := ℂ)).eigenvalues_eq i
    set b := (Matrix.isHermitian_one (n := Fin d) (α := ℂ)).eigenvectorBasis i
    have hnorm : ‖b‖ = 1 :=
      (Matrix.isHermitian_one (n := Fin d) (α := ℂ)).eigenvectorBasis.orthonormal.1 i
    have h2 : (inner ℂ b b : ℂ) = b.ofLp ⬝ᵥ star b.ofLp :=
      EuclideanSpace.inner_eq_star_dotProduct _ _
    have h3 : (inner ℂ b b : ℂ) = 1 := by
      rw [inner_self_eq_norm_sq_to_K, hnorm]
      simp
    rw [Matrix.one_mulVec] at h1
    rw [h1, dotProduct_comm, ← h2, h3]
    simp
  simp [posIndex, posIndexAbove, h]

end Zeta23Redux.LinAlg

