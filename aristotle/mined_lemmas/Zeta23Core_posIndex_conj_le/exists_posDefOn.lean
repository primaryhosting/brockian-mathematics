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
