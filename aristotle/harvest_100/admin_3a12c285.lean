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

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

open Matrix

namespace Zeta23Core

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The positive index of inertia of a Hermitian matrix: the number of (indices carrying a)
positive eigenvalue. -/
noncomputable def posIndex {A : Matrix n n 𝕜} (hA : A.IsHermitian) : ℕ :=
  Fintype.card {i : n // 0 < hA.eigenvalues i}

omit [DecidableEq n] in
/-- Changing coordinates by a matrix `U` in the quadratic form attached to `A = U * (D * Uᴴ)`. -/
theorem quad_conj (A U D : Matrix n n 𝕜) (hA : A = U * (D * star U)) (x : n → 𝕜) :
    star x ⬝ᵥ (A *ᵥ x) = star (star U *ᵥ x) ⬝ᵥ (D *ᵥ (star U *ᵥ x)) := by
  subst hA
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]
  simp [Matrix.mulVec_mulVec, ← mul_assoc, Matrix.star_eq_conjTranspose]

/-- The real part of the quadratic form of a real diagonal matrix. -/
theorem re_quad_diagonal (d : n → ℝ) (y : n → 𝕜) :
    RCLike.re (star y ⬝ᵥ (Matrix.diagonal (RCLike.ofReal ∘ d) *ᵥ y)) = ∑ i, d i * ‖y i‖ ^ 2 := by
  rw [dotProduct, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mulVec_diagonal]
  simp [RCLike.star_def, mul_comm, ← RCLike.normSq_eq_def', RCLike.normSq_apply]
  ring

/-- Diagonalization of a Hermitian matrix, in the form `A = U * (D * Uᴴ)`. -/
theorem spectral_conj {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    A = (hA.eigenvectorUnitary : Matrix n n 𝕜) *
      (Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) *
        star (hA.eigenvectorUnitary : Matrix n n 𝕜)) := by
  conv_lhs => rw [hA.spectral_theorem]
  simp [Unitary.conjStarAlgAut_apply, mul_assoc]

/-- The real quadratic form of a Hermitian matrix, expressed in the eigenbasis coordinates. -/
theorem re_quad_eq_sum {A : Matrix n n 𝕜} (hA : A.IsHermitian) (x : n → 𝕜) :
    RCLike.re (star x ⬝ᵥ (A *ᵥ x)) =
      ∑ i, hA.eigenvalues i *
        ‖(star (hA.eigenvectorUnitary : Matrix n n 𝕜) *ᵥ x) i‖ ^ 2 := by
  rw [quad_conj A _ _ (spectral_conj hA) x, re_quad_diagonal]

/-- **Sylvester's law of inertia, hard direction.**  If a Hermitian matrix `A` over an `RCLike`
field is positive definite on a subspace `W` of `n → 𝕜`, then the dimension of `W` is at most
the number of positive eigenvalues of `A`. -/
theorem sylvester_finrank_le_posIndex {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (W : Submodule 𝕜 (n → 𝕜))
    (hW : ∀ x ∈ W, x ≠ 0 → 0 < RCLike.re (star x ⬝ᵥ (A *ᵥ x))) :
    Module.finrank 𝕜 W ≤ posIndex hA := by
  set U : Matrix n n 𝕜 := ↑hA.eigenvectorUnitary with hU
  -- the coordinates of `x` in the eigenbasis, restricted to the positive eigenvalues
  set f : (n → 𝕜) →ₗ[𝕜] ({i : n // 0 < hA.eigenvalues i} → 𝕜) :=
    (LinearMap.funLeft 𝕜 𝕜 (Subtype.val : {i : n // 0 < hA.eigenvalues i} → n)).comp
      (Matrix.mulVecLin (star U)) with hf
  have hinj : Function.Injective ⇑(f.comp W.subtype) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    rintro ⟨x, hx⟩ hker
    have hker' : ∀ i : n, 0 < hA.eigenvalues i → (star U *ᵥ x) i = 0 := by
      intro i hi
      have := congrFun (LinearMap.mem_ker.1 hker) ⟨i, hi⟩
      simpa [hf, LinearMap.funLeft_apply] using this
    have hle : RCLike.re (star x ⬝ᵥ (A *ᵥ x)) ≤ 0 := by
      rw [re_quad_eq_sum hA x]
      refine Finset.sum_nonpos fun i _ => ?_
      rcases lt_or_ge 0 (hA.eigenvalues i) with hi | hi
      · rw [← hU, hker' i hi]
        simp
      · exact mul_nonpos_of_nonpos_of_nonneg hi (by positivity)
    have hx0 : x = 0 := by
      by_contra hne
      exact absurd hle (not_le.2 (hW x hx hne))
    exact Submodule.mk_eq_zero _ _ |>.2 hx0
  calc Module.finrank 𝕜 W
      ≤ Module.finrank 𝕜 ({i : n // 0 < hA.eigenvalues i} → 𝕜) :=
        LinearMap.finrank_le_finrank_of_injective hinj
    _ = posIndex hA := Module.finrank_fintype_fun_eq_card 𝕜

end Zeta23Core

