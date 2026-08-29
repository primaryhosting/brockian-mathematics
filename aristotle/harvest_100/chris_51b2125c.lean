/-
# Pos Index Conj Le
Category: Brockian Corpus
Target: Zeta23Core.posIndex_conj_le
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Zeta23Core

open Matrix

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The real quadratic form `x ↦ xᴴ Q x` associated with a square matrix `Q`
(for Hermitian `Q` the value `xᴴ Q x` is real, and `qform` records its real part). -/
def qform {m : Type*} [Fintype m] (Q : Matrix m m 𝕜) (x : m → 𝕜) : ℝ :=
  RCLike.re (star x ⬝ᵥ Q *ᵥ x)

/-- The positive index of inertia `n₊(Q)` of a Hermitian matrix `Q`: the number of
positive eigenvalues, counted with multiplicity.  (For non-Hermitian `Q` it is `0`.) -/
noncomputable def posIndex {m : Type*} [Fintype m] [DecidableEq m] (Q : Matrix m m 𝕜) : ℕ :=
  if h : Q.IsHermitian then Nat.card {i // 0 < h.eigenvalues i} else 0

theorem posIndex_of_isHermitian {m : Type*} [Fintype m] [DecidableEq m] {Q : Matrix m m 𝕜}
    (hQ : Q.IsHermitian) : posIndex Q = Nat.card {i // 0 < hQ.eigenvalues i} := by
  simp [posIndex, hQ]

/-- Compressing a matrix corresponds to precomposing its quadratic form with `B`. -/
theorem qform_compress {m d : Type*} [Fintype m] [Fintype d] (Q : Matrix m m 𝕜)
    (B : Matrix m d 𝕜) (y : d → 𝕜) : qform (Bᴴ * Q * B) y = qform Q (B *ᵥ y) := by
  unfold qform
  congr 1
  simp [Matrix.star_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_vecMul]

/-- The quadratic form of a real diagonal matrix. -/
theorem qform_diagonal {m : Type*} [Fintype m] [DecidableEq m] (dd : m → ℝ) (y : m → 𝕜) :
    qform (diagonal (RCLike.ofReal ∘ dd) : Matrix m m 𝕜) y = ∑ i, dd i * ‖y i‖ ^ 2 := by
  have key : (star y ⬝ᵥ ((diagonal (RCLike.ofReal ∘ dd) : Matrix m m 𝕜) *ᵥ y))
      = ∑ i, ((dd i * ‖y i‖ ^ 2 : ℝ) : 𝕜) := by
    rw [dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mulVec, diagonal_dotProduct, Pi.star_apply]
    have h2 : star (y i) * ((RCLike.ofReal ∘ dd) i * y i) = (dd i : 𝕜) * (y i * star (y i)) := by
      simp [RCLike.star_def]; ring
    rw [h2, RCLike.star_def, RCLike.mul_conj]
    push_cast
    ring
  unfold qform
  rw [key]
  simp [map_sum]

section Spectral

variable {m : Type*} [Fintype m] [DecidableEq m] {Q : Matrix m m 𝕜}

/-- Diagonalisation: `Uᴴ Q U` is the diagonal matrix of eigenvalues. -/
theorem conjTranspose_mul_mul_eigenvectorUnitary (hQ : Q.IsHermitian) :
    (hQ.eigenvectorUnitary : Matrix m m 𝕜)ᴴ * Q * (hQ.eigenvectorUnitary : Matrix m m 𝕜)
      = diagonal (RCLike.ofReal ∘ hQ.eigenvalues) := by
  have h := hQ.conjStarAlgAut_star_eigenvectorUnitary
  rw [Unitary.conjStarAlgAut_star_apply] at h
  simpa [mul_assoc] using h

/-- The spectral expansion of the quadratic form: with `z = Uᴴ x` the coordinates of `x`
in the eigenbasis, `xᴴ Q x = ∑ λᵢ ‖zᵢ‖²`. -/
theorem qform_eq_sum_eigenvalues (hQ : Q.IsHermitian) (x : m → 𝕜) :
    qform Q x = ∑ i, hQ.eigenvalues i *
      ‖((hQ.eigenvectorUnitary : Matrix m m 𝕜)ᴴ *ᵥ x) i‖ ^ 2 := by
  set U : Matrix m m 𝕜 := (hQ.eigenvectorUnitary : Matrix m m 𝕜) with hU
  have hUs : Uᴴ * U = 1 := by
    simpa [hU, Matrix.star_eq_conjTranspose] using
      Unitary.coe_star_mul_self hQ.eigenvectorUnitary
  have hsU : U * Uᴴ = 1 := by
    simpa [hU, Matrix.star_eq_conjTranspose] using
      Unitary.coe_mul_star_self hQ.eigenvectorUnitary
  have hx : U *ᵥ (Uᴴ *ᵥ x) = x := by
    rw [Matrix.mulVec_mulVec, hsU, Matrix.one_mulVec]
  calc qform Q x = qform Q (U *ᵥ (Uᴴ *ᵥ x)) := by rw [hx]
    _ = qform (Uᴴ * Q * U) (Uᴴ *ᵥ x) := (qform_compress Q U _).symm
    _ = qform (diagonal (RCLike.ofReal ∘ hQ.eigenvalues) : Matrix m m 𝕜) (Uᴴ *ᵥ x) := by
        rw [conjTranspose_mul_mul_eigenvectorUnitary hQ]
    _ = _ := qform_diagonal _ _

end Spectral

/-- If a linear map out of `m → 𝕜` is injective on a submodule `S`, then the dimension of `S`
is at most the dimension of the target. -/
theorem finrank_le_of_injOn {m : Type*} [Fintype m] {N : Type*} [AddCommGroup N] [Module 𝕜 N]
    [Module.Finite 𝕜 N] (S : Submodule 𝕜 (m → 𝕜)) (f : (m → 𝕜) →ₗ[𝕜] N)
    (hf : ∀ y ∈ S, f y = 0 → y = 0) : Module.finrank 𝕜 S ≤ Module.finrank 𝕜 N := by
  refine LinearMap.finrank_le_finrank_of_injective (f := f.comp S.subtype) ?_
  intro a b hab
  have h0 : f (a - b : S) = 0 := by
    have : f (a : m → 𝕜) = f (b : m → 𝕜) := hab
    simp [map_sub, this]
  have := hf ((a : m → 𝕜) - b) (S.sub_mem a.2 b.2) (by simpa using h0)
  exact Subtype.ext (sub_eq_zero.mp this)

section Main

variable {m d : Type*} [Fintype m] [DecidableEq m] [Fintype d] [DecidableEq d]

/-- **Direction B (hard direction of Sylvester's law), in compressed form.**
If the quadratic form of `Q` is positive on the (nonzero vectors of the) image of a subspace
`S` under `B`, then `dim S ≤ n₊(Q)`. -/
theorem finrank_le_posIndex_of_pos_on_image {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian)
    (B : Matrix m d 𝕜) (S : Submodule 𝕜 (d → 𝕜))
    (hS : ∀ y ∈ S, y ≠ 0 → 0 < qform Q (B *ᵥ y)) :
    Module.finrank 𝕜 S ≤ posIndex Q := by
  classical
  set P := {i : m // 0 < hQ.eigenvalues i} with hP
  haveI : Fintype P := Fintype.ofFinite P
  set U : Matrix m m 𝕜 := (hQ.eigenvectorUnitary : Matrix m m 𝕜) with hU
  set f : (d → 𝕜) →ₗ[𝕜] (P → 𝕜) :=
    (LinearMap.funLeft 𝕜 𝕜 (Subtype.val : P → m)).comp (Matrix.toLin' (Uᴴ * B)) with hf
  have hcard : Module.finrank 𝕜 (P → 𝕜) = posIndex Q := by
    rw [Module.finrank_fintype_fun_eq_card, posIndex_of_isHermitian hQ, Nat.card_eq_fintype_card]
  rw [← hcard]
  refine finrank_le_of_injOn S f ?_
  intro y hy hy0
  by_contra hne
  have hpos := hS y hy hne
  have hzero : ∀ i : P, (Uᴴ *ᵥ (B *ᵥ y)) (i : m) = 0 := by
    intro i
    have h1 : ((Uᴴ * B) *ᵥ y) (i : m) = 0 := congrFun hy0 i
    rwa [← Matrix.mulVec_mulVec] at h1
  have hsum := qform_eq_sum_eigenvalues hQ (B *ᵥ y)
  have hle : qform Q (B *ᵥ y) ≤ 0 := by
    rw [hsum]
    refine Finset.sum_nonpos fun i _ => ?_
    by_cases hi : 0 < hQ.eigenvalues i
    · have hz : (Uᴴ *ᵥ (B *ᵥ y)) i = 0 := hzero ⟨i, hi⟩
      rw [hz]
      simp
    · exact mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hi) (by positivity)
  linarith

/-- **Direction A.** There is a subspace of dimension `n₊(Q)` on which `Q` is positive definite. -/
theorem exists_posDef_subspace {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian) :
    ∃ S : Submodule 𝕜 (m → 𝕜), Module.finrank 𝕜 S = posIndex Q ∧
      ∀ x ∈ S, x ≠ 0 → 0 < qform Q x := by
  classical
  set P := {i : m // 0 < hQ.eigenvalues i} with hP
  haveI : Fintype P := Fintype.ofFinite P
  set U : Matrix m m 𝕜 := (hQ.eigenvectorUnitary : Matrix m m 𝕜) with hU
  have hUs : Uᴴ * U = 1 := by
    simpa [hU, Matrix.star_eq_conjTranspose] using
      Unitary.coe_star_mul_self hQ.eigenvectorUnitary
  -- extension by zero from the positive coordinates
  set ext : (P → 𝕜) →ₗ[𝕜] (m → 𝕜) :=
    LinearMap.pi (fun i : m => if h : 0 < hQ.eigenvalues i then
      (LinearMap.proj (⟨i, h⟩ : P) : (P → 𝕜) →ₗ[𝕜] 𝕜) else 0) with hext
  have hext_apply : ∀ (z : P → 𝕜) (i : m),
      ext z i = if h : 0 < hQ.eigenvalues i then z ⟨i, h⟩ else 0 := by
    intro z i
    rw [hext]
    by_cases h : 0 < hQ.eigenvalues i
    · simp only [LinearMap.pi_apply, dif_pos h]
      rfl
    · simp [h]
  set ι : (P → 𝕜) →ₗ[𝕜] (m → 𝕜) := (Matrix.toLin' U).comp ext with hι
  have hext_inj : Function.Injective ext := by
    intro z w h
    funext i
    have h1 := congrFun h (i : m)
    rw [hext_apply, hext_apply, dif_pos i.2, dif_pos i.2] at h1
    simpa using h1
  have hU_inj : Function.Injective (fun v : m → 𝕜 => U *ᵥ v) := by
    intro v w h
    have : Uᴴ *ᵥ (U *ᵥ v) = Uᴴ *ᵥ (U *ᵥ w) := by simp only [h]
    rwa [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hUs, Matrix.one_mulVec,
      Matrix.one_mulVec] at this
  have hι_inj : Function.Injective ι := by
    intro z w h
    refine hext_inj (hU_inj ?_)
    simpa [hι, Matrix.toLin'_apply] using h
  refine ⟨LinearMap.range ι, ?_, ?_⟩
  · rw [LinearMap.finrank_range_of_inj hι_inj, Module.finrank_fintype_fun_eq_card,
      posIndex_of_isHermitian hQ, Nat.card_eq_fintype_card]
  · rintro x ⟨z, rfl⟩ hx0
    have hcoord : Uᴴ *ᵥ (ι z) = ext z := by
      simp only [hι, LinearMap.comp_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec, hUs,
        Matrix.one_mulVec]
    rw [qform_eq_sum_eigenvalues hQ, hcoord]
    have hzne : ext z ≠ 0 := by
      intro h
      apply hx0
      simp only [hι, LinearMap.comp_apply, Matrix.toLin'_apply, h, Matrix.mulVec_zero]
    obtain ⟨i0, hi0⟩ : ∃ i, ext z i ≠ 0 := by
      by_contra h
      exact hzne (funext fun i => by simpa using not_not.mp (not_exists.mp h i))
    have hi0pos : 0 < hQ.eigenvalues i0 := by
      by_contra h
      exact hi0 (by rw [hext_apply]; simp [h])
    refine Finset.sum_pos' (fun i _ => ?_) ⟨i0, Finset.mem_univ _, ?_⟩
    · by_cases h : 0 < hQ.eigenvalues i
      · positivity
      · have hz : ext z i = 0 := by rw [hext_apply]; simp [h]
        simp [hz]
    · have : ‖ext z i0‖ ≠ 0 := norm_ne_zero_iff.mpr hi0
      have h2 : 0 < ‖ext z i0‖ ^ 2 := by positivity
      exact mul_pos hi0pos h2

/-- **Inertia does not increase under compression:** for a Hermitian matrix `Q` and any
rectangular matrix `B`, the compression `Bᴴ Q B` is Hermitian and `n₊(Bᴴ Q B) ≤ n₊(Q)`. -/
theorem posIndex_conj_le {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian) (B : Matrix m d 𝕜) :
    (Bᴴ * Q * B).IsHermitian ∧ posIndex (Bᴴ * Q * B) ≤ posIndex Q := by
  refine ⟨isHermitian_conjTranspose_mul_mul B hQ, ?_⟩
  obtain ⟨S, hSdim, hSpos⟩ := exists_posDef_subspace (isHermitian_conjTranspose_mul_mul B hQ)
  have := finrank_le_posIndex_of_pos_on_image hQ B S (fun y hy hy0 => by
    have := hSpos y hy hy0
    rwa [qform_compress] at this)
  rwa [hSdim] at this

/-- Sanity check: the identity matrix has full positive index. -/
theorem posIndex_one : posIndex (1 : Matrix m m 𝕜) = Fintype.card m := by
  classical
  have hHerm : (1 : Matrix m m 𝕜).IsHermitian := isHermitian_one
  have hdiag : (1 : Matrix m m 𝕜) = diagonal (RCLike.ofReal ∘ fun _ : m => (1 : ℝ)) := by
    have h : (RCLike.ofReal ∘ fun _ : m => (1 : ℝ)) = fun _ : m => (1 : 𝕜) := by
      funext i; simp
    rw [h, Matrix.diagonal_one]
  have hqform : ∀ y : m → 𝕜, qform (1 : Matrix m m 𝕜) y = ∑ i, ‖y i‖ ^ 2 := by
    intro y
    rw [hdiag, qform_diagonal]
    simp
  refine le_antisymm ?_ ?_
  · rw [posIndex_of_isHermitian hHerm, ← Nat.card_eq_fintype_card]
    exact Nat.card_le_card_of_injective _ Subtype.val_injective
  · have hle := finrank_le_posIndex_of_pos_on_image hHerm (1 : Matrix m m 𝕜)
      (⊤ : Submodule 𝕜 (m → 𝕜)) (fun y _ hy0 => by
        rw [Matrix.one_mulVec, hqform]
        obtain ⟨i0, hi0⟩ : ∃ i, y i ≠ 0 := by
          by_contra h
          exact hy0 (funext fun i => not_not.mp (not_exists.mp h i))
        refine Finset.sum_pos' (fun i _ => by positivity) ⟨i0, Finset.mem_univ _, ?_⟩
        have : ‖y i0‖ ≠ 0 := norm_ne_zero_iff.mpr hi0
        positivity)
    rwa [finrank_top, Module.finrank_fintype_fun_eq_card] at hle

end Main

end Zeta23Core

