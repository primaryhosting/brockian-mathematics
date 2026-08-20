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
