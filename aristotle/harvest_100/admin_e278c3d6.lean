/-
# Sylvester Finrank Le Pos Index
Category: Brockian Corpus
Target: Zeta23Core.sylvester_finrank_le_posIndex
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sylvester Finrank Le Pos Index
Category: Brockian Corpus
Target: Zeta23Core.sylvester_finrank_le_posIndex
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Zeta23Core

open Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The positive index of inertia of a Hermitian matrix: the number of positive eigenvalues. -/
noncomputable def posIndex {A : Matrix n n 𝕜} (hA : A.IsHermitian) : ℕ :=
  Fintype.card {i : n // 0 < hA.eigenvalues i}

/-- The Hermitian quadratic form of `A` expressed in the eigenbasis coordinates
`y = Uᴴ x`, where `U` is the eigenvector unitary. -/
theorem quadraticForm_eq_sum_eigenvalues {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (x : n → 𝕜) :
    RCLike.re (star x ⬝ᵥ A *ᵥ x) =
      ∑ i, hA.eigenvalues i *
        ‖((star (hA.eigenvectorUnitary : Matrix n n 𝕜)) *ᵥ x) i‖ ^ 2 := by
  set U : Matrix n n 𝕜 := (hA.eigenvectorUnitary : Matrix n n 𝕜) with hU
  set y : n → 𝕜 := (star U) *ᵥ x with hy
  have hstar : star x ᵥ* U = star y := by
    rw [hy, Matrix.star_mulVec]
    congr 1
    simp [← Matrix.star_eq_conjTranspose]
  have hA' : A = U * Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) * star U := by
    conv_lhs => rw [hA.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply]
  have key : star x ⬝ᵥ A *ᵥ x
      = star y ⬝ᵥ (Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) *ᵥ y) := by
    conv_lhs => rw [hA']
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, hstar]
  rw [key, dotProduct, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mulVec_diagonal]
  have h : star y i * ((RCLike.ofReal ∘ hA.eigenvalues) i * y i)
      = ((hA.eigenvalues i : 𝕜)) * ((starRingEnd 𝕜) (y i) * y i) := by
    simp [RCLike.star_def]; ring
  rw [h, RCLike.conj_mul]
  rw [show ((‖y i‖ : 𝕜)) ^ 2 = ((‖y i‖ ^ 2 : ℝ) : 𝕜) by push_cast; ring]
  simp

/-- **Sylvester's law of inertia (hard direction).**
If a Hermitian matrix `A` over an `RCLike` field induces a positive definite quadratic form
on a submodule `W` of `n → 𝕜`, then `dim W ≤ n₊(A)`, the number of positive eigenvalues
of `A`. -/
theorem sylvester_finrank_le_posIndex {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (W : Submodule 𝕜 (n → 𝕜))
    (hW : ∀ x ∈ W, x ≠ 0 → 0 < RCLike.re (star x ⬝ᵥ A *ᵥ x)) :
    Module.finrank 𝕜 W ≤ posIndex hA := by
  classical
  set U : Matrix n n 𝕜 := (hA.eigenvectorUnitary : Matrix n n 𝕜)
  set P : Type _ := {i : n // 0 < hA.eigenvalues i}
  set f : (n → 𝕜) →ₗ[𝕜] (P → 𝕜) :=
    (LinearMap.funLeft 𝕜 𝕜 (Subtype.val : P → n)).comp (Matrix.mulVecLin (star U)) with hf
  have hinj : Function.Injective ⇑(f.comp W.subtype) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    rintro ⟨x, hx⟩ hker
    have hzero : ∀ i : n, 0 < hA.eigenvalues i → ((star U) *ᵥ x) i = 0 := by
      intro i hi
      have := congrFun (congrArg (fun g => (g : P → 𝕜)) (LinearMap.mem_ker.mp hker)) ⟨i, hi⟩
      simpa [hf, LinearMap.funLeft, Matrix.mulVecLin] using this
    have hle : RCLike.re (star x ⬝ᵥ A *ᵥ x) ≤ 0 := by
      rw [quadraticForm_eq_sum_eigenvalues hA x]
      refine Finset.sum_nonpos fun i _ => ?_
      rcases lt_or_ge 0 (hA.eigenvalues i) with hi | hi
      · rw [hzero i hi]
        simp
      · exact mul_nonpos_of_nonpos_of_nonneg hi (by positivity)
    refine Subtype.ext ?_
    by_contra hne
    exact absurd hle (not_le.mpr (hW x hx hne))
  have hbound := LinearMap.finrank_le_finrank_of_injective (R := 𝕜) hinj
  rw [Module.finrank_fintype_fun_eq_card] at hbound
  exact hbound

end Zeta23Core

