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

open Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {m d : Type*} [Fintype m] [Fintype d]

/-- The real quadratic form associated with a matrix: `x ↦ re (xᴴ Q x)`. -/
def qform (Q : Matrix m m 𝕜) (x : m → 𝕜) : ℝ := RCLike.re (star x ⬝ᵥ Q *ᵥ x)

/-- `Q` is positive definite on the subspace `S`. -/
def PosDefOn (Q : Matrix m m 𝕜) (S : Submodule 𝕜 (m → 𝕜)) : Prop :=
  ∀ x ∈ S, x ≠ 0 → 0 < qform Q x

/-- The positive inertia index of a Hermitian matrix: the number of positive eigenvalues
(and `0` for non-Hermitian matrices). -/
noncomputable def posIndex [DecidableEq m] (Q : Matrix m m 𝕜) : ℕ :=
  if h : Q.IsHermitian then Nat.card {i // 0 < h.eigenvalues i} else 0

lemma posIndex_of_isHermitian [DecidableEq m] {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian) :
    posIndex Q = Nat.card {i // 0 < hQ.eigenvalues i} := dif_pos hQ

/-- The quadratic form of a compression. -/
lemma qform_conj (Q : Matrix m m 𝕜) (B : Matrix m d 𝕜) (y : d → 𝕜) :
    qform (Bᴴ * Q * B) y = qform Q (B *ᵥ y) := by
  simp [qform, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.star_mulVec]

/-- The quadratic form of a real diagonal matrix. -/
lemma qform_diagonal [DecidableEq m] (lam : m → ℝ) (y : m → 𝕜) :
    qform (diagonal (fun i => (RCLike.ofReal (lam i) : 𝕜))) y = ∑ i, lam i * ‖y i‖ ^ 2 := by
  rw [qform, dotProduct, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : (diagonal (fun i => (RCLike.ofReal (lam i) : 𝕜))) *ᵥ y = fun i =>
      (RCLike.ofReal (lam i) : 𝕜) * y i := by
    funext j; simp [Matrix.mulVec_diagonal]
  rw [h1]
  have h2 : star (y i) * ((RCLike.ofReal (lam i) : 𝕜) * y i)
      = (RCLike.ofReal (lam i) : 𝕜) * (star (y i) * y i) := by ring
  simp only [Pi.star_apply, h2]
  simp [RCLike.star_def, RCLike.conj_mul]

omit [Fintype d] in
/-- Compressions of Hermitian matrices are Hermitian. -/
lemma isHermitian_conj {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian) (B : Matrix m d 𝕜) :
    (Bᴴ * Q * B).IsHermitian := by
  simp [Matrix.IsHermitian, Matrix.conjTranspose_mul, hQ.eq, Matrix.mul_assoc]

/-- The unitary `V` of eigenvectors diagonalizes `Q`: `Vᴴ Q V` is the diagonal matrix of
eigenvalues. -/
lemma conjTranspose_mul_mul_eigenvectorUnitary [DecidableEq m] {Q : Matrix m m 𝕜}
    (hQ : Q.IsHermitian) :
    (hQ.eigenvectorUnitary : Matrix m m 𝕜)ᴴ * Q * (hQ.eigenvectorUnitary : Matrix m m 𝕜)
      = diagonal (fun i => (RCLike.ofReal (hQ.eigenvalues i) : 𝕜)) := by
  have h := hQ.conjStarAlgAut_star_eigenvectorUnitary (𝕜 := 𝕜)
  rw [Unitary.conjStarAlgAut_star_apply] at h
  simpa [Matrix.star_eq_conjTranspose, Function.comp] using h

lemma eigenvectorUnitary_mulVec_conjTranspose_mulVec [DecidableEq m] {Q : Matrix m m 𝕜}
    (hQ : Q.IsHermitian) (x : m → 𝕜) :
    (hQ.eigenvectorUnitary : Matrix m m 𝕜) *ᵥ ((hQ.eigenvectorUnitary : Matrix m m 𝕜)ᴴ *ᵥ x)
      = x := by
  rw [Matrix.mulVec_mulVec]
  have h : (hQ.eigenvectorUnitary : Matrix m m 𝕜) * (hQ.eigenvectorUnitary : Matrix m m 𝕜)ᴴ = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Unitary.mul_star_self_of_mem hQ.eigenvectorUnitary.2
  rw [h, Matrix.one_mulVec]

lemma conjTranspose_mulVec_eigenvectorUnitary_mulVec [DecidableEq m] {Q : Matrix m m 𝕜}
    (hQ : Q.IsHermitian) (y : m → 𝕜) :
    (hQ.eigenvectorUnitary : Matrix m m 𝕜)ᴴ *ᵥ ((hQ.eigenvectorUnitary : Matrix m m 𝕜) *ᵥ y)
      = y := by
  rw [Matrix.mulVec_mulVec]
  have h : (hQ.eigenvectorUnitary : Matrix m m 𝕜)ᴴ * (hQ.eigenvectorUnitary : Matrix m m 𝕜) = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Unitary.star_mul_self_of_mem hQ.eigenvectorUnitary.2
  rw [h, Matrix.one_mulVec]

/-- Diagonalization of the quadratic form of a Hermitian matrix. -/
lemma qform_eq_sum_eigenvalues [DecidableEq m] {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian)
    (x : m → 𝕜) :
    qform Q x
      = ∑ i, hQ.eigenvalues i * ‖((hQ.eigenvectorUnitary : Matrix m m 𝕜)ᴴ *ᵥ x) i‖ ^ 2 := by
  calc qform Q x
      = qform Q ((hQ.eigenvectorUnitary : Matrix m m 𝕜) *ᵥ
          ((hQ.eigenvectorUnitary : Matrix m m 𝕜)ᴴ *ᵥ x)) := by
        rw [eigenvectorUnitary_mulVec_conjTranspose_mulVec hQ]
    _ = qform ((hQ.eigenvectorUnitary : Matrix m m 𝕜)ᴴ * Q * (hQ.eigenvectorUnitary :
 Matrix m m 𝕜))
          ((hQ.eigenvectorUnitary : Matrix m m 𝕜)ᴴ *ᵥ x) :=
        (qform_conj Q _ _).symm
    _ = _ := by
        rw [conjTranspose_mul_mul_eigenvectorUnitary hQ, qform_diagonal]

/-- **Sylvester, hard direction**: any subspace on which `Q` is positive definite has dimension
at most the positive inertia index of `Q`. -/
lemma finrank_le_posIndex [DecidableEq m] {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian)
    {S : Submodule 𝕜 (m → 𝕜)} (hS : PosDefOn Q S) :
    Module.finrank 𝕜 S ≤ posIndex Q := by
  classical
  set V : Matrix m m 𝕜 := (hQ.eigenvectorUnitary : Matrix m m 𝕜) with hV
  set f : (m → 𝕜) →ₗ[𝕜] ({i : m // 0 < hQ.eigenvalues i} → 𝕜) :=
    (LinearMap.funLeft 𝕜 𝕜 (Subtype.val : {i : m // 0 < hQ.eigenvalues i} → m)).comp
      (Matrix.mulVecLin Vᴴ) with hf
  have hinj : Function.Injective (f.domRestrict S) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    rintro ⟨x, hx⟩ hx0
    have hzero : ∀ i : m, 0 < hQ.eigenvalues i → (Vᴴ *ᵥ x) i = 0 := by
      intro i hi
      have := congrFun (congrArg (fun z => (z : {i : m // 0 < hQ.eigenvalues i} → 𝕜))
        (LinearMap.mem_ker.mp hx0)) ⟨i, hi⟩
      simpa [hf, LinearMap.funLeft] using this
    by_contra hne
    have hxne : x ≠ 0 := by simpa [Subtype.ext_iff] using hne
    have hpos := hS x hx hxne
    rw [qform_eq_sum_eigenvalues hQ] at hpos
    have hnp : ∑ i, hQ.eigenvalues i * ‖(Vᴴ *ᵥ x) i‖ ^ 2 ≤ 0 := by
      refine Finset.sum_nonpos fun i _ => ?_
      rcases lt_or_ge 0 (hQ.eigenvalues i) with hi | hi
      · simp [hzero i hi]
      · exact mul_nonpos_of_nonpos_of_nonneg hi (by positivity)
    exact absurd hpos (not_lt.mpr hnp)
  have h1 : Module.finrank 𝕜 S ≤ Module.finrank 𝕜 ({i : m // 0 < hQ.eigenvalues i} → 𝕜) :=
    LinearMap.finrank_le_finrank_of_injective hinj
  rw [posIndex_of_isHermitian hQ, Nat.card_eq_fintype_card]
  simpa [Module.finrank_fintype_fun_eq_card] using h1

/-- **Sylvester, easy direction**: there is a subspace of dimension `posIndex Q` on which `Q`
is positive definite. -/
lemma exists_posDefOn [DecidableEq m] {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian) :
    ∃ S : Submodule 𝕜 (m → 𝕜), Module.finrank 𝕜 S = posIndex Q ∧ PosDefOn Q S := by
  classical
  set V : Matrix m m 𝕜 := (hQ.eigenvectorUnitary : Matrix m m 𝕜) with hV
  set E : ({i : m // 0 < hQ.eigenvalues i} → 𝕜) →ₗ[𝕜] (m → 𝕜) :=
    Function.ExtendByZero.linearMap 𝕜 (Subtype.val : {i : m // 0 < hQ.eigenvalues i} → m) with hE
  set g : ({i : m // 0 < hQ.eigenvalues i} → 𝕜) →ₗ[𝕜] (m → 𝕜) :=
    (Matrix.mulVecLin V).comp E with hg
  have hVinj : Function.Injective (Matrix.mulVecLin V) := by
    have : Function.LeftInverse (fun y : m → 𝕜 => Vᴴ *ᵥ y) (fun y : m → 𝕜 => V *ᵥ y) :=
      fun y => conjTranspose_mulVec_eigenvectorUnitary_mulVec hQ y
    exact this.injective
  have hEinj : Function.Injective E :=
    Function.extend_injective Subtype.val_injective (0 : m → 𝕜)
  have hginj : Function.Injective g := hVinj.comp hEinj
  have hVg : ∀ c, Vᴴ *ᵥ (g c) = E c := by
    intro c
    simpa [hg] using conjTranspose_mulVec_eigenvectorUnitary_mulVec hQ (E c)
  have hEval : ∀ (c : {i : m // 0 < hQ.eigenvalues i} → 𝕜) (j : {i : m // 0 < hQ.eigenvalues i}),
      E c j.1 = c j := by
    intro c j
    simp [hE]
  have hEzero : ∀ (c : {i : m // 0 < hQ.eigenvalues i} → 𝕜) (i : m), ¬ (0 < hQ.eigenvalues i) →
      E c i = 0 := by
    intro c i hi
    have : ¬ ∃ j : {i : m // 0 < hQ.eigenvalues i}, (j : m) = i := by
      rintro ⟨⟨j, hj⟩, rfl⟩; exact hi hj
    simpa [hE] using Function.extend_apply' (f := (Subtype.val :
      {i : m // 0 < hQ.eigenvalues i} → m)) c 0 i this
  refine ⟨LinearMap.range g, ?_, ?_⟩
  · rw [posIndex_of_isHermitian hQ, Nat.card_eq_fintype_card,
      ← Module.finrank_fintype_fun_eq_card (R := 𝕜) (η := {i : m // 0 < hQ.eigenvalues i})]
    exact ((LinearEquiv.ofInjective g hginj).finrank_eq).symm
  · rintro x hx hx0
    obtain ⟨c, rfl⟩ := LinearMap.mem_range.mp hx
    have hcne : c ≠ 0 := by rintro rfl; simp at hx0
    obtain ⟨j, hj⟩ : ∃ j, c j ≠ 0 := Function.ne_iff.mp hcne
    rw [qform_eq_sum_eigenvalues hQ]
    have hterm : ∀ i ∈ Finset.univ, 0 ≤ hQ.eigenvalues i * ‖(Vᴴ *ᵥ g c) i‖ ^ 2 := by
      intro i _
      rcases lt_or_ge 0 (hQ.eigenvalues i) with hi | hi
      · positivity
      · rw [hVg c, hEzero c i (not_lt.mpr hi)]
        simp
    refine Finset.sum_pos' hterm ⟨j.1, Finset.mem_univ _, ?_⟩
    rw [hVg c, hEval c j]
    have h1 : (0 : ℝ) < ‖c j‖ ^ 2 := by positivity
    exact mul_pos j.2 h1

/-- Sanity check: the identity matrix has full positive inertia index. -/
lemma posIndex_one [DecidableEq m] : posIndex (1 : Matrix m m 𝕜) = Fintype.card m := by
  classical
  have hH : (1 : Matrix m m 𝕜).IsHermitian := Matrix.isHermitian_one
  have hpos : PosDefOn (1 : Matrix m m 𝕜) ⊤ := by
    intro x _ hx
    have h1 : (1 : Matrix m m 𝕜) = diagonal (fun _ => (RCLike.ofReal (1 : ℝ) : 𝕜)) := by simp
    obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := Function.ne_iff.mp hx
    rw [h1, qform_diagonal]
    refine Finset.sum_pos' (fun i _ => by positivity) ⟨j, Finset.mem_univ _, ?_⟩
    have : (0 : ℝ) < ‖x j‖ ^ 2 := by positivity
    simpa using this
  have hle : Fintype.card m ≤ posIndex (1 : Matrix m m 𝕜) := by
    have := finrank_le_posIndex hH hpos
    simpa [Module.finrank_fintype_fun_eq_card] using this
  have hge : posIndex (1 : Matrix m m 𝕜) ≤ Fintype.card m := by
    rw [posIndex_of_isHermitian hH, Nat.card_eq_fintype_card]
    exact Fintype.card_subtype_le _
  exact le_antisymm hge hle

/-- **Inertia does not increase under compression**: for a Hermitian `Q` and any rectangular
matrix `B`, the compression `Bᴴ Q B` is Hermitian and `n₊(Bᴴ Q B) ≤ n₊(Q)`. -/
theorem posIndex_conj_le [DecidableEq m] [DecidableEq d] {Q : Matrix m m 𝕜}
    (hQ : Q.IsHermitian) (B : Matrix m d 𝕜) :
    (Bᴴ * Q * B).IsHermitian ∧ posIndex (Bᴴ * Q * B) ≤ posIndex Q := by
  refine ⟨isHermitian_conj hQ B, ?_⟩
  obtain ⟨S, hdim, hpos⟩ := exists_posDefOn (isHermitian_conj hQ B)
  set f : (d → 𝕜) →ₗ[𝕜] (m → 𝕜) := Matrix.mulVecLin B with hf
  have hinj : Function.Injective (f.domRestrict S) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    rintro ⟨y, hy⟩ hy0
    have h0 : B *ᵥ y = 0 := by simpa [hf, LinearMap.domRestrict] using hy0
    by_contra hne
    have hyne : y ≠ 0 := by simpa [Subtype.ext_iff] using hne
    have := hpos y hy hyne
    rw [qform_conj, h0] at this
    simp [qform] at this
  have hmap : S.map f = LinearMap.range (f.domRestrict S) := (LinearMap.range_domRestrict S f).symm
  have hposT : PosDefOn Q (S.map f) := by
    rintro x hx hx0
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
    have hyne : y ≠ 0 := by rintro rfl; simp [hf] at hx0
    have := hpos y hy hyne
    rwa [qform_conj] at this
  have h1 : Module.finrank 𝕜 S = Module.finrank 𝕜 (S.map f) := by
    rw [hmap]
    exact (LinearEquiv.ofInjective _ hinj).finrank_eq
  calc posIndex (Bᴴ * Q * B) = Module.finrank 𝕜 S := hdim.symm
    _ = Module.finrank 𝕜 (S.map f) := h1
    _ ≤ posIndex Q := finrank_le_posIndex hQ hposT

end Zeta23Core

