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

/-!
## Inertia does not increase under compression

For a Hermitian matrix `Q` on a finite type `m` and a rectangular matrix `B : Matrix m d 𝕜`, the
compression `Bᴴ * Q * B` is Hermitian and its positive index of inertia (the number of positive
eigenvalues, counted with multiplicity) is at most that of `Q`.

The proof follows the variational route.  Writing `qform Q x = Re (xᴴ Q x)`, we prove both
directions of the (finite dimensional) Sylvester characterisation of the positive index:

* `Zeta23Core.exists_posdef_matrix`: the column space of `U * posProj` — where `U` diagonalises `Q`
  and `posProj` projects onto the positive eigen-directions — is a subspace of dimension
  `posIndex Q` on which `qform Q` is positive definite;
* `Zeta23Core.finrank_le_posIndex`: any subspace on which `qform Q` is positive definite has
  dimension at most `posIndex Q` (it meets the "non-positive" subspace `ker (posProj * Uᴴ)`
  trivially, and that kernel has codimension `posIndex Q`).

For the compression, such a subspace for `Bᴴ Q B` is pushed forward by `B`; injectivity on it is
forced by positive definiteness, so the dimension is preserved.
-/

namespace Zeta23Core

open Matrix Module

section Defs

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The (real) quadratic form `x ↦ Re (xᴴ Q x)` attached to a matrix `Q`. -/

theorem posIndex_conj_le {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian) (B : Matrix m d 𝕜) :
    posIndex (Bᴴ * Q * B) ≤ posIndex Q := by
  obtain ⟨C, hCrank, hCpos⟩ := exists_posdef_matrix (isHermitian_conj hQ B)
  set G : Matrix m d 𝕜 := B * C with hG
  have hGC : ∀ c : d → 𝕜, G *ᵥ c = B *ᵥ (C *ᵥ c) := fun c => by rw [hG, mulVec_mulVec]
  have hqG : ∀ c : d → 𝕜, qform Q (G *ᵥ c) = qform (Bᴴ * Q * B) (C *ᵥ c) := fun c => by
    rw [hGC, qform_conj]
  have hCne : ∀ c : d → 𝕜, G *ᵥ c ≠ 0 → C *ᵥ c ≠ 0 := by
    intro c hc h0
    exact hc (by rw [hGC, h0, mulVec_zero])
  have hkereq : LinearMap.ker (Matrix.mulVecLin G) = LinearMap.ker (Matrix.mulVecLin C) := by
    apply le_antisymm
    · intro c hc
      simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hc ⊢
      by_contra h
      have hpos := hCpos c h
      rw [← hqG c, hc, qform_zero] at hpos
      exact lt_irrefl _ hpos
    · intro c hc
      simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hc ⊢
      rw [hGC, hc, mulVec_zero]
  have hrank : G.rank = C.rank := by
    have h1 := LinearMap.finrank_range_add_finrank_ker (K := 𝕜) (Matrix.mulVecLin G)
    have h2 := LinearMap.finrank_range_add_finrank_ker (K := 𝕜) (Matrix.mulVecLin C)
    rw [hkereq] at h1
    unfold Matrix.rank
    omega
  have hSpos : ∀ x ∈ LinearMap.range (Matrix.mulVecLin G), x ≠ 0 → 0 < qform Q x := by
    rintro x ⟨c, rfl⟩ hx
    simp only [Matrix.mulVecLin_apply] at hx ⊢
    rw [hqG c]
    exact hCpos c (hCne c hx)
  have hle := finrank_le_posIndex hQ _ hSpos
  rwa [show finrank 𝕜 (LinearMap.range (Matrix.mulVecLin G)) = G.rank from rfl, hrank,
    hCrank] at hle

/-- Sanity check (non-vacuity): the positive index of the `3 × 3` identity matrix is `3`. -/
