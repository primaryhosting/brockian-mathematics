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
