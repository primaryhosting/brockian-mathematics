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

namespace Zeta23Core

open Matrix Module

variable {𝕜 : Type*} [RCLike 𝕜] {m d : Type*} [Fintype m] [DecidableEq m]
  [Fintype d] [DecidableEq d]

/-- The (real) quadratic form associated with a matrix `Q`: `x ↦ Re (xᴴ Q x)`. -/
noncomputable def qform (Q : Matrix m m 𝕜) (x : m → 𝕜) : ℝ :=
  RCLike.re (star x ⬝ᵥ Q *ᵥ x)

/-- The positive index of inertia of a Hermitian matrix: the number of positive eigenvalues
(counted with multiplicity).  It is set to `0` for non-Hermitian matrices. -/
noncomputable def posIndex (Q : Matrix m m 𝕜) : ℕ :=
  if h : Q.IsHermitian then
    (Finset.univ.filter fun i => 0 < h.eigenvalues i).card
  else 0

/-- `Q` is positive definite on the subspace `S`. -/
def IsPosOn (Q : Matrix m m 𝕜) (S : Submodule 𝕜 (m → 𝕜)) : Prop :=
  ∀ x ∈ S, x ≠ 0 → 0 < qform Q x

omit [DecidableEq m] [DecidableEq d] in
/-- The quadratic form of a compression, evaluated at `y`, is the quadratic form of the original
matrix evaluated at `M *ᵥ y`. -/
lemma qform_conj (Q : Matrix m m 𝕜) (M : Matrix m d 𝕜) (y : d → 𝕜) :
    qform Q (M *ᵥ y) = qform (Mᴴ * Q * M) y := by
  unfold qform
  rw [mulVec_mulVec, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, Matrix.mul_assoc]

/-- The coordinate subspace of vectors supported in `s`. -/
def coordSub (s : Finset m) : Submodule 𝕜 (m → 𝕜) where
  carrier := {x | ∀ i ∉ s, x i = 0}
  add_mem' := by
    intro a b ha hb i hi
    simp [ha i hi, hb i hi]
  zero_mem' := by intro i _; rfl
  smul_mem' := by
    intro c a ha i hi
    simp [ha i hi]

omit [Fintype m] [DecidableEq m] in
@[simp] lemma mem_coordSub {s : Finset m} {x : m → 𝕜} :
    x ∈ (coordSub s : Submodule 𝕜 (m → 𝕜)) ↔ ∀ i ∉ s, x i = 0 := Iff.rfl

/-- The coordinate subspace supported in `s` is isomorphic to `s → 𝕜`. -/
noncomputable def coordEquiv (s : Finset m) : (coordSub (𝕜 := 𝕜) s) ≃ₗ[𝕜] (s → 𝕜) where
  toFun x i := (x : m → 𝕜) i
  map_add' := by intros; rfl
  map_smul' := by intros; rfl
  invFun y := ⟨fun i => if h : i ∈ s then y ⟨i, h⟩ else 0, by intro i hi; simp [hi]⟩
  left_inv := by
    intro x
    ext i
    by_cases h : i ∈ s
    · simp [h]
    · simp [h, x.2 i h]
  right_inv := by
    intro y
    ext i
    simp

omit [Fintype m] in
lemma finrank_coordSub (s : Finset m) :
    finrank 𝕜 (coordSub (𝕜 := 𝕜) s) = s.card := by
  rw [(coordEquiv (𝕜 := 𝕜) s).finrank_eq, Module.finrank_fintype_fun_eq_card, Fintype.card_coe]

/-- The quadratic form of a diagonal matrix. -/
lemma qform_diagonal (c : m → ℝ) (y : m → 𝕜) :
    qform (Matrix.diagonal (RCLike.ofReal ∘ c) : Matrix m m 𝕜) y = ∑ i, c i * ‖y i‖ ^ 2 := by
  simp only [qform, dotProduct, Matrix.mulVec_diagonal, Function.comp_apply,
    Pi.star_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : star (y i) * ((c i : 𝕜) * y i) = ((c i * ‖y i‖ ^ 2 : ℝ) : 𝕜) := by
    rw [show star (y i) = (starRingEnd 𝕜) (y i) from rfl, mul_comm ((c i : 𝕜)) (y i),
      ← mul_assoc, RCLike.conj_mul]
    push_cast; ring
  rw [h, RCLike.ofReal_re]

/-- Conjugating by the eigenvector unitary diagonalizes a Hermitian matrix. -/
lemma conj_eigenvectorUnitary {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian) :
    (hQ.eigenvectorUnitary : Matrix m m 𝕜)ᴴ * Q * (hQ.eigenvectorUnitary : Matrix m m 𝕜)
      = Matrix.diagonal (RCLike.ofReal ∘ hQ.eigenvalues) := by
  have h := hQ.conjStarAlgAut_star_eigenvectorUnitary
  rw [Unitary.conjStarAlgAut_star_apply] at h
  simpa using h

/-- The quadratic form of `Q` in the eigenvector coordinates. -/
lemma qform_eigen {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian) (y : m → 𝕜) :
    qform Q ((hQ.eigenvectorUnitary : Matrix m m 𝕜) *ᵥ y)
      = ∑ i, hQ.eigenvalues i * ‖y i‖ ^ 2 := by
  rw [qform_conj, conj_eigenvectorUnitary hQ, qform_diagonal]

lemma mulVecLin_eigenvectorUnitary_injective {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian) :
    Function.Injective (Matrix.mulVecLin (hQ.eigenvectorUnitary : Matrix m m 𝕜)) := by
  intro a b hab
  have h1 : (star (hQ.eigenvectorUnitary : Matrix m m 𝕜)) *
      (hQ.eigenvectorUnitary : Matrix m m 𝕜) = 1 := Unitary.coe_star_mul_self _
  have h2 : (star (hQ.eigenvectorUnitary : Matrix m m 𝕜)) *ᵥ
        ((hQ.eigenvectorUnitary : Matrix m m 𝕜) *ᵥ a)
      = (star (hQ.eigenvectorUnitary : Matrix m m 𝕜)) *ᵥ
        ((hQ.eigenvectorUnitary : Matrix m m 𝕜) *ᵥ b) := by
    simpa [Matrix.mulVecLin] using
      congrArg (fun v => (star (hQ.eigenvectorUnitary : Matrix m m 𝕜)) *ᵥ v) hab
  rwa [mulVec_mulVec, mulVec_mulVec, h1, one_mulVec, one_mulVec] at h2

/-- The span of the eigenvectors indexed by `s`. -/
noncomputable def eigenSub {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian) (s : Finset m) :
    Submodule 𝕜 (m → 𝕜) :=
  Submodule.map (Matrix.mulVecLin (hQ.eigenvectorUnitary : Matrix m m 𝕜)) (coordSub s)

lemma finrank_eigenSub {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian) (s : Finset m) :
    finrank 𝕜 (eigenSub hQ s) = s.card := by
  rw [eigenSub, ← (Submodule.equivMapOfInjective _ (mulVecLin_eigenvectorUnitary_injective hQ)
    (coordSub s)).finrank_eq, finrank_coordSub]

/-- On the span of the eigenvectors with positive eigenvalue, `Q` is positive definite. -/
lemma isPosOn_eigenSub {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian) :
    IsPosOn Q (eigenSub hQ (Finset.univ.filter fun i => 0 < hQ.eigenvalues i)) := by
  rintro _ ⟨y, hy, rfl⟩ hne
  have hy0 : y ≠ 0 := by rintro rfl; simp at hne
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hy0
  rw [Matrix.mulVecLin_apply, qform_eigen]
  refine Finset.sum_pos' (fun j _ => ?_) ⟨i, Finset.mem_univ i, ?_⟩
  · by_cases hj : j ∈ Finset.univ.filter fun i => 0 < hQ.eigenvalues i
    · have : 0 < hQ.eigenvalues j := by simpa using (Finset.mem_filter.mp hj).2
      exact mul_nonneg this.le (sq_nonneg _)
    · rw [hy j hj]; simp
  · have hi' : i ∈ Finset.univ.filter fun i => 0 < hQ.eigenvalues i := by
      by_contra h
      exact hi (hy i h)
    have hpos : 0 < hQ.eigenvalues i := by simpa using (Finset.mem_filter.mp hi').2
    exact mul_pos hpos (pow_pos (norm_pos_iff.mpr hi) 2)

/-- On the span of the eigenvectors with non-positive eigenvalue, `Q` is negative semidefinite. -/
lemma qform_nonpos_eigenSub {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian)
    (x : m → 𝕜) (hx : x ∈ eigenSub hQ (Finset.univ.filter fun i => ¬ 0 < hQ.eigenvalues i)) :
    qform Q x ≤ 0 := by
  obtain ⟨y, hy, rfl⟩ := hx
  rw [Matrix.mulVecLin_apply, qform_eigen]
  refine Finset.sum_nonpos fun j _ => ?_
  by_cases hj : j ∈ Finset.univ.filter fun i => ¬ 0 < hQ.eigenvalues i
  · have h : hQ.eigenvalues j ≤ 0 := by
      have := (Finset.mem_filter.mp hj).2
      simpa using not_lt.mp this
    have h2 : (0:ℝ) ≤ ‖y j‖ ^ 2 := sq_nonneg _
    nlinarith
  · rw [hy j hj]; simp

/-- Existence of a positive definite subspace of dimension `posIndex Q`. -/
lemma exists_isPosOn {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian) :
    ∃ S : Submodule 𝕜 (m → 𝕜), IsPosOn Q S ∧ finrank 𝕜 S = posIndex Q := by
  refine ⟨eigenSub hQ (Finset.univ.filter fun i => 0 < hQ.eigenvalues i),
    isPosOn_eigenSub hQ, ?_⟩
  rw [finrank_eigenSub, posIndex, dif_pos hQ]

/-- Sylvester, hard direction: any subspace on which `Q` is positive definite has dimension at
most `posIndex Q`. -/
lemma finrank_le_posIndex {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian)
    (S : Submodule 𝕜 (m → 𝕜)) (hS : IsPosOn Q S) :
    finrank 𝕜 S ≤ posIndex Q := by
  have hinf : S ⊓ eigenSub hQ (Finset.univ.filter fun i => ¬ 0 < hQ.eigenvalues i) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    by_contra hx0
    have h1 := hS x hx.1 hx0
    have h2 := qform_nonpos_eigenSub hQ x hx.2
    linarith
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq S
    (eigenSub hQ (Finset.univ.filter fun i => ¬ 0 < hQ.eigenvalues i))
  rw [hinf, finrank_bot, add_zero] at hsum
  have hle : finrank 𝕜 ↥(S ⊔ eigenSub hQ (Finset.univ.filter fun i => ¬ 0 < hQ.eigenvalues i))
      ≤ Fintype.card m := by
    have h := Submodule.finrank_le
      (S ⊔ eigenSub hQ (Finset.univ.filter fun i => ¬ 0 < hQ.eigenvalues i))
    simpa [Module.finrank_fintype_fun_eq_card] using h
  have hN : finrank 𝕜 (eigenSub hQ (Finset.univ.filter fun i => ¬ 0 < hQ.eigenvalues i))
      = (Finset.univ.filter fun i => ¬ 0 < hQ.eigenvalues i).card := finrank_eigenSub hQ _
  have hcard : (Finset.univ.filter fun i => 0 < hQ.eigenvalues i).card
      + (Finset.univ.filter fun i => ¬ 0 < hQ.eigenvalues i).card = Fintype.card m :=
    Finset.card_filter_add_card_filter_not _
  rw [posIndex, dif_pos hQ]
  omega

/-- **Inertia does not increase under compression.**  For a Hermitian matrix `Q` and any
rectangular matrix `B`, the compression `Bᴴ * Q * B` is Hermitian and its positive index of
inertia is at most that of `Q`. -/
theorem posIndex_conj_le {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian) (B : Matrix m d 𝕜) :
    (Bᴴ * Q * B).IsHermitian ∧ posIndex (Bᴴ * Q * B) ≤ posIndex Q := by
  have hP : (Bᴴ * Q * B).IsHermitian := by
    simp [Matrix.IsHermitian, Matrix.conjTranspose_mul, hQ.eq, Matrix.mul_assoc]
  refine ⟨hP, ?_⟩
  obtain ⟨S, hS, hdim⟩ := exists_isPosOn hP
  have hker : LinearMap.ker ((Matrix.mulVecLin B).domRestrict S) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    rintro ⟨y, hy⟩ hy0
    by_contra hne
    have hy1 : y ≠ 0 := by
      intro h
      exact hne (Subtype.ext h)
    have h1 := hS y hy hy1
    have h2 : B *ᵥ y = 0 := by simpa [Matrix.mulVecLin] using hy0
    rw [← qform_conj, h2] at h1
    simp [qform] at h1
  have hTpos : IsPosOn Q (Submodule.map (Matrix.mulVecLin B) S) := by
    rintro _ ⟨y, hy, rfl⟩ hne
    have hy0 : y ≠ 0 := by rintro rfl; simp at hne
    rw [Matrix.mulVecLin_apply, qform_conj]
    exact hS y hy hy0
  have hdimT : finrank 𝕜 (Submodule.map (Matrix.mulVecLin B) S) = finrank 𝕜 S := by
    rw [← LinearMap.range_domRestrict]
    exact LinearMap.finrank_range_of_inj (LinearMap.ker_eq_bot.mp hker)
  calc posIndex (Bᴴ * Q * B) = finrank 𝕜 S := hdim.symm
    _ = finrank 𝕜 (Submodule.map (Matrix.mulVecLin B) S) := hdimT.symm
    _ ≤ posIndex Q := finrank_le_posIndex hQ _ hTpos

end Zeta23Core

