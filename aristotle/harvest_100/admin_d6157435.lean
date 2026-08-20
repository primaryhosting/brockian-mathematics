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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Zeta23Core

open Matrix Module

variable {𝕜 : Type*} [RCLike 𝕜] {m d : Type*} [Fintype m] [DecidableEq m] [Fintype d]
  [DecidableEq d]

/-- The real quadratic form `x ↦ xᴴ Q x` attached to a matrix `Q`. -/
noncomputable def qform (Q : Matrix m m 𝕜) (x : m → 𝕜) : ℝ :=
  RCLike.re (star x ⬝ᵥ Q *ᵥ x)

omit [DecidableEq m] in
@[simp] lemma qform_zero (Q : Matrix m m 𝕜) : qform Q 0 = 0 := by
  simp [qform]

/-- `Q` is positive definite on the subspace `S`. -/
def PosDefOn (Q : Matrix m m 𝕜) (S : Submodule 𝕜 (m → 𝕜)) : Prop :=
  ∀ x ∈ S, x ≠ 0 → 0 < qform Q x

/-- The positive index of inertia `n₊(Q)`: the number of positive eigenvalues of a Hermitian
matrix (and `0` for a non-Hermitian matrix). -/
noncomputable def posIndex (Q : Matrix m m 𝕜) : ℕ :=
  if h : Q.IsHermitian then Fintype.card {i // 0 < h.eigenvalues i} else 0

lemma posIndex_of_isHermitian {Q : Matrix m m 𝕜} (h : Q.IsHermitian) :
    posIndex Q = Fintype.card {i // 0 < h.eigenvalues i} := by
  simp [posIndex, h]

omit [DecidableEq m] [DecidableEq d] in
/-- The quadratic form of a compression `BᴴQB` is the quadratic form of `Q` along `B`. -/
lemma qform_conj (Q : Matrix m m 𝕜) (B : Matrix m d 𝕜) (x : d → 𝕜) :
    qform (Bᴴ * Q * B) x = qform Q (B *ᵥ x) := by
  unfold qform
  congr 1
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    ← Matrix.star_mulVec]

/-- Coordinate subspace: the vectors whose coordinates vanish on `{i | p i}`. -/
noncomputable def coordKer (p : m → Prop) : Submodule 𝕜 (m → 𝕜) :=
  LinearMap.ker (LinearMap.funLeft 𝕜 𝕜 (Subtype.val : {i // p i} → m))

omit [Fintype m] [DecidableEq m] in
lemma mem_coordKer {p : m → Prop} {y : m → 𝕜} :
    y ∈ (coordKer p : Submodule 𝕜 (m → 𝕜)) ↔ ∀ i, p i → y i = 0 := by
  simp [coordKer, LinearMap.mem_ker, funext_iff, Subtype.forall]

omit [DecidableEq m] in
lemma finrank_coordKer (p : m → Prop) :
    finrank 𝕜 (coordKer p : Submodule 𝕜 (m → 𝕜)) = Fintype.card m - Fintype.card {i // p i} := by
  have hsurj : Function.Surjective (LinearMap.funLeft 𝕜 𝕜 (Subtype.val : {i // p i} → m)) :=
    LinearMap.funLeft_surjective_of_injective _ _ _ Subtype.val_injective
  have h := LinearMap.finrank_range_add_finrank_ker
    (LinearMap.funLeft 𝕜 𝕜 (Subtype.val : {i // p i} → m))
  rw [LinearMap.range_eq_top.2 hsurj] at h
  simp only [finrank_top, Module.finrank_pi] at h
  simp only [coordKer]
  omega

/-- The quadratic form of a real diagonal matrix. -/
lemma qform_diagonal (μ : m → ℝ) (y : m → 𝕜) :
    qform (Matrix.diagonal (RCLike.ofReal ∘ μ) : Matrix m m 𝕜) y = ∑ i, μ i * ‖y i‖ ^ 2 := by
  unfold qform
  rw [dotProduct, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mulVec_diagonal]
  have hstep : star (y i) * ((RCLike.ofReal ∘ μ) i * y i) = ((μ i * ‖y i‖ ^ 2 : ℝ) : 𝕜) := by
    have h := RCLike.conj_mul (y i)
    simp only [Function.comp_apply, RCLike.star_def]
    rw [show (RCLike.ofReal (μ i) * y i) = y i * RCLike.ofReal (μ i) from mul_comm _ _,
      ← mul_assoc, h]
    push_cast
    ring
  rw [Pi.star_apply, hstep, RCLike.ofReal_re]

lemma qform_diagonal_pos (μ : m → ℝ) {y : m → 𝕜}
    (hy : y ∈ (coordKer (fun i => ¬ 0 < μ i) : Submodule 𝕜 (m → 𝕜))) (hy0 : y ≠ 0) :
    0 < qform (Matrix.diagonal (RCLike.ofReal ∘ μ) : Matrix m m 𝕜) y := by
  rw [mem_coordKer] at hy
  rw [qform_diagonal]
  obtain ⟨j, hj⟩ : ∃ j, y j ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hy0 (funext hcon)
  have hμj : 0 < μ j := by
    by_contra hcon
    exact hj (hy j hcon)
  refine Finset.sum_pos' (fun i _ => ?_) ⟨j, Finset.mem_univ j, ?_⟩
  · rcases lt_or_ge 0 (μ i) with h | h
    · positivity
    · have : y i = 0 := hy i (by simpa using h)
      simp [this]
  · have : 0 < ‖y j‖ ^ 2 := by positivity
    exact mul_pos hμj this

lemma qform_diagonal_nonpos (μ : m → ℝ) {y : m → 𝕜}
    (hy : y ∈ (coordKer (fun i => 0 < μ i) : Submodule 𝕜 (m → 𝕜))) :
    qform (Matrix.diagonal (RCLike.ofReal ∘ μ) : Matrix m m 𝕜) y ≤ 0 := by
  rw [mem_coordKer] at hy
  rw [qform_diagonal]
  refine Finset.sum_nonpos fun i _ => ?_
  rcases lt_or_ge 0 (μ i) with h | h
  · simp [hy i h]
  · exact mul_nonpos_of_nonpos_of_nonneg h (by positivity)

/-- Multiplication by an invertible matrix, as a linear equivalence. -/
noncomputable def mulVecEquiv {A A' : Matrix m m 𝕜} (h₁ : A * A' = 1) (h₂ : A' * A = 1) :
    (m → 𝕜) ≃ₗ[𝕜] (m → 𝕜) :=
  LinearEquiv.ofLinear A.mulVecLin A'.mulVecLin
    (LinearMap.ext fun x => by simp [Matrix.mulVecLin, Matrix.mulVec_mulVec, h₁])
    (LinearMap.ext fun x => by simp [Matrix.mulVecLin, Matrix.mulVec_mulVec, h₂])

@[simp] lemma mulVecEquiv_apply {A A' : Matrix m m 𝕜} (h₁ : A * A' = 1) (h₂ : A' * A = 1)
    (x : m → 𝕜) : mulVecEquiv h₁ h₂ x = A *ᵥ x := rfl

/-- Congruence invariance of the quadratic form under the unitary change of coordinates
provided by the spectral theorem. -/
lemma qform_spectral {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian) (y : m → 𝕜) :
    qform Q ((hQ.eigenvectorUnitary : Matrix m m 𝕜) *ᵥ y)
      = qform (Matrix.diagonal (RCLike.ofReal ∘ hQ.eigenvalues) : Matrix m m 𝕜) y := by
  set U : Matrix m m 𝕜 := (hQ.eigenvectorUnitary : Matrix m m 𝕜) with hU
  set D : Matrix m m 𝕜 := Matrix.diagonal (RCLike.ofReal ∘ hQ.eigenvalues) with hD
  have hspec : Q = U * D * star U := hQ.spectral_theorem
  have hUU : star U * U = 1 := Matrix.UnitaryGroup.star_mul_self hQ.eigenvectorUnitary
  have hQU : Q * U = U * D := by rw [hspec, mul_assoc, mul_assoc, hUU, mul_one]
  unfold qform
  congr 1
  rw [Matrix.mulVec_mulVec, hQU, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.star_mulVec, Matrix.vecMul_vecMul]
  have hUh : Uᴴ * U = 1 := by rw [← Matrix.star_eq_conjTranspose]; exact hUU
  rw [hUh, Matrix.vecMul_one]

lemma eigenvectorUnitary_mul_star {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian) :
    (hQ.eigenvectorUnitary : Matrix m m 𝕜) * star (hQ.eigenvectorUnitary : Matrix m m 𝕜) = 1 :=
  (Unitary.mem_iff.1 hQ.eigenvectorUnitary.2).2

lemma card_pos_le {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian) :
    Fintype.card {i // 0 < hQ.eigenvalues i} ≤ Fintype.card m :=
  Fintype.card_subtype_le _

/-- Easy direction of Sylvester's law: there is a subspace of dimension `n₊(Q)` on which
`Q` is positive definite. -/
lemma exists_posDefOn {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian) :
    ∃ S : Submodule 𝕜 (m → 𝕜), finrank 𝕜 S = posIndex Q ∧ PosDefOn Q S := by
  set U : Matrix m m 𝕜 := (hQ.eigenvectorUnitary : Matrix m m 𝕜) with hU
  have hUU : star U * U = 1 := Matrix.UnitaryGroup.star_mul_self hQ.eigenvectorUnitary
  have hUU' : U * star U = 1 := eigenvectorUnitary_mul_star hQ
  set e : (m → 𝕜) ≃ₗ[𝕜] (m → 𝕜) := mulVecEquiv hUU' hUU with he
  set P : Submodule 𝕜 (m → 𝕜) := coordKer (fun i => ¬ 0 < hQ.eigenvalues i) with hP
  refine ⟨P.map (e : (m → 𝕜) →ₗ[𝕜] (m → 𝕜)), ?_, ?_⟩
  · rw [LinearEquiv.finrank_map_eq, hP, finrank_coordKer, posIndex_of_isHermitian hQ,
      Fintype.card_subtype_compl]
    have := card_pos_le hQ
    omega
  · rintro x hx hx0
    rw [Submodule.mem_map] at hx
    obtain ⟨y, hyP, rfl⟩ := hx
    have hy0 : y ≠ 0 := by
      rintro rfl
      exact hx0 (by simp)
    have : (e : (m → 𝕜) →ₗ[𝕜] (m → 𝕜)) y = U *ᵥ y := rfl
    rw [this, qform_spectral hQ]
    exact qform_diagonal_pos _ hyP hy0

/-- Hard direction of Sylvester's law: any subspace on which `Q` is positive definite has
dimension at most `n₊(Q)`. -/
lemma finrank_le_posIndex {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian) (S : Submodule 𝕜 (m → 𝕜))
    (hS : PosDefOn Q S) : finrank 𝕜 S ≤ posIndex Q := by
  set U : Matrix m m 𝕜 := (hQ.eigenvectorUnitary : Matrix m m 𝕜) with hU
  have hUU : star U * U = 1 := Matrix.UnitaryGroup.star_mul_self hQ.eigenvectorUnitary
  have hUU' : U * star U = 1 := eigenvectorUnitary_mul_star hQ
  set e : (m → 𝕜) ≃ₗ[𝕜] (m → 𝕜) := mulVecEquiv hUU' hUU with he
  set S' : Submodule 𝕜 (m → 𝕜) := S.map (e.symm : (m → 𝕜) →ₗ[𝕜] (m → 𝕜)) with hS'
  have hrank : finrank 𝕜 S' = finrank 𝕜 S := LinearEquiv.finrank_map_eq e.symm S
  -- `Q` in the eigenbasis coordinates is positive definite on `S'`
  have hS'pos : ∀ y ∈ S', y ≠ 0 →
      0 < qform (Matrix.diagonal (RCLike.ofReal ∘ hQ.eigenvalues) : Matrix m m 𝕜) y := by
    rintro y hy hy0
    rw [hS', Submodule.mem_map] at hy
    obtain ⟨x, hxS, hxy⟩ := hy
    have hx : U *ᵥ y = x := by
      rw [← hxy]
      exact e.apply_symm_apply x
    have hx0 : x ≠ 0 := by
      rintro rfl
      apply hy0
      rw [← hxy]
      simp
    rw [← qform_spectral hQ y, hx]
    exact hS x hxS hx0
  set N : Submodule 𝕜 (m → 𝕜) := coordKer (fun i => 0 < hQ.eigenvalues i) with hN
  have hinf : S' ⊓ N = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro y ⟨hy1, hy2⟩
    by_contra hy0
    have h1 := hS'pos y hy1 hy0
    have h2 := qform_diagonal_nonpos hQ.eigenvalues hy2
    linarith
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq S' N
  rw [hinf, finrank_bot, add_zero] at hsup
  have hle : finrank 𝕜 (S' ⊔ N : Submodule 𝕜 (m → 𝕜)) ≤ Fintype.card m := by
    have := Submodule.finrank_le (S' ⊔ N : Submodule 𝕜 (m → 𝕜))
    simpa [Module.finrank_pi] using this
  have hNrank : finrank 𝕜 N = Fintype.card m - Fintype.card {i // 0 < hQ.eigenvalues i} := by
    rw [hN, finrank_coordKer]
  rw [posIndex_of_isHermitian hQ]
  have hcard := card_pos_le hQ
  omega

/-- Inertia does not increase under compression: `n₊(BᴴQB) ≤ n₊(Q)`. -/
theorem posIndex_conj_le {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian) (B : Matrix m d 𝕜) :
    (Bᴴ * Q * B).IsHermitian ∧ posIndex (Bᴴ * Q * B) ≤ posIndex Q := by
  refine ⟨Matrix.isHermitian_conjTranspose_mul_mul B hQ, ?_⟩
  obtain ⟨S, hSrank, hSpos⟩ := exists_posDefOn (Matrix.isHermitian_conjTranspose_mul_mul B hQ)
  set f : (d → 𝕜) →ₗ[𝕜] (m → 𝕜) := B.mulVecLin with hf
  set g : S →ₗ[𝕜] (m → 𝕜) := f ∘ₗ S.subtype with hg
  have hker : LinearMap.ker g = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro ⟨z, hzS⟩ hz
    have hBz : B *ᵥ z = 0 := by simpa [hg, hf, Matrix.mulVecLin] using hz
    have : z = 0 := by
      by_contra hz0
      have := hSpos z hzS hz0
      rw [qform_conj Q B z, hBz, qform_zero] at this
      exact lt_irrefl 0 this
    simp [this]
  have hrange : LinearMap.range g = S.map f := by
    rw [hg, LinearMap.range_comp, Submodule.range_subtype]
  have hfin := LinearMap.finrank_range_add_finrank_ker g
  rw [hker, finrank_bot, add_zero, hrange] at hfin
  have hpos : PosDefOn Q (S.map f) := by
    rintro x hx hx0
    rw [Submodule.mem_map] at hx
    obtain ⟨z, hzS, rfl⟩ := hx
    have hz0 : z ≠ 0 := by
      rintro rfl
      exact hx0 (by simp)
    have : f z = B *ᵥ z := rfl
    rw [this, ← qform_conj Q B z]
    exact hSpos z hzS hz0
  have := finrank_le_posIndex hQ (S.map f) hpos
  omega

end Zeta23Core

