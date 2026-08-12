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

namespace Zeta23Core

open Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The positive index (number of positive eigenvalues) of a Hermitian matrix. -/
noncomputable def posIndex {A : Matrix n n 𝕜} (hA : A.IsHermitian) : ℕ :=
  Fintype.card {i : n // 0 < hA.eigenvalues i}

/-- Diagonalization of a Hermitian matrix, written multiplicatively. -/
lemma isHermitian_eq_unitary_mul_diagonal {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    A = (hA.eigenvectorUnitary : Matrix n n 𝕜) *
      (diagonal (RCLike.ofReal ∘ hA.eigenvalues)) *
      star (hA.eigenvectorUnitary : Matrix n n 𝕜) := by
  conv_lhs => rw [hA.spectral_theorem]
  simp [Unitary.conjStarAlgAut_apply]

/-- The Hermitian form of `A` in the eigenbasis coordinates. -/
lemma dotProduct_mulVec_eq_diagonal {A : Matrix n n 𝕜} (hA : A.IsHermitian) (x : n → 𝕜) :
    star x ⬝ᵥ (A *ᵥ x)
      = star (star (hA.eigenvectorUnitary : Matrix n n 𝕜) *ᵥ x) ⬝ᵥ
        (diagonal (RCLike.ofReal ∘ hA.eigenvalues) *ᵥ
          (star (hA.eigenvectorUnitary : Matrix n n 𝕜) *ᵥ x)) := by
  rw [star_mulVec, Matrix.star_eq_conjTranspose, conjTranspose_conjTranspose,
    ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, ← Matrix.star_eq_conjTranspose,
    ← isHermitian_eq_unitary_mul_diagonal hA]

/-- The real part of a diagonal Hermitian form is a weighted sum of squared norms. -/
lemma re_dotProduct_diagonal (d : n → ℝ) (y : n → 𝕜) :
    RCLike.re (star y ⬝ᵥ (diagonal (RCLike.ofReal ∘ d) *ᵥ y)) = ∑ i, d i * ‖y i‖ ^ 2 := by
  rw [dotProduct, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mulVec_diagonal]
  simp only [Pi.star_apply, Function.comp_apply, ← mul_assoc]
  rw [show star (y i) * (RCLike.ofReal (d i) : 𝕜)
      = (RCLike.ofReal (d i) : 𝕜) * star (y i) from mul_comm _ _]
  rw [mul_assoc, RCLike.mul_re]
  simp [RCLike.star_def, RCLike.conj_mul]

/-- The Hermitian form of `A` evaluated at `x` equals `∑ λ i * ‖y i‖ ^ 2`, where `y` are the
coordinates of `x` in the eigenbasis. -/
lemma re_dotProduct_mulVec_eq_sum {A : Matrix n n 𝕜} (hA : A.IsHermitian) (x : n → 𝕜) :
    RCLike.re (star x ⬝ᵥ (A *ᵥ x))
      = ∑ i, hA.eigenvalues i *
          ‖(star (hA.eigenvectorUnitary : Matrix n n 𝕜) *ᵥ x) i‖ ^ 2 := by
  rw [dotProduct_mulVec_eq_diagonal hA x, re_dotProduct_diagonal]

/-- The linear map sending `x` to the eigenbasis coordinates of `x` indexed by the positive
eigenvalues. -/
noncomputable def posCoords {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    (n → 𝕜) →ₗ[𝕜] ({i : n // 0 < hA.eigenvalues i} → 𝕜) :=
  (LinearMap.funLeft 𝕜 𝕜 (Subtype.val : {i : n // 0 < hA.eigenvalues i} → n)).comp
    (Matrix.mulVecLin (star (hA.eigenvectorUnitary : Matrix n n 𝕜)))

lemma posCoords_apply {A : Matrix n n 𝕜} (hA : A.IsHermitian) (x : n → 𝕜)
    (i : {i : n // 0 < hA.eigenvalues i}) :
    posCoords hA x i = (star (hA.eigenvectorUnitary : Matrix n n 𝕜) *ᵥ x) i.1 := rfl

/-- **Sylvester's law of inertia**, hard direction: any subspace on which the Hermitian form
of `A` is positive definite has dimension at most the number of positive eigenvalues of `A`. -/
theorem sylvester_finrank_le_posIndex {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (W : Submodule 𝕜 (n → 𝕜))
    (hW : ∀ x ∈ W, x ≠ 0 → 0 < RCLike.re (star x ⬝ᵥ (A *ᵥ x))) :
    Module.finrank 𝕜 W ≤ posIndex hA := by
  set T : W →ₗ[𝕜] ({i : n // 0 < hA.eigenvalues i} → 𝕜) := (posCoords hA).comp W.subtype with hT
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨x, hx⟩ hx0
    have hzero : ∀ i : n, 0 < hA.eigenvalues i →
        (star (hA.eigenvectorUnitary : Matrix n n 𝕜) *ᵥ x) i = 0 := by
      intro i hi
      have := congrFun hx0 ⟨i, hi⟩
      simpa [hT, posCoords_apply] using this
    have hsum : RCLike.re (star x ⬝ᵥ (A *ᵥ x)) ≤ 0 := by
      rw [re_dotProduct_mulVec_eq_sum hA x]
      refine Finset.sum_nonpos fun i _ => ?_
      rcases lt_or_ge 0 (hA.eigenvalues i) with hi | hi
      · simp [hzero i hi]
      · exact mul_nonpos_of_nonpos_of_nonneg hi (by positivity)
    have hx' : x = 0 := by
      by_contra hne
      exact absurd hsum (not_le.mpr (hW x hx hne))
    exact Subtype.ext hx'
  have hle := LinearMap.finrank_le_finrank_of_injective (f := T) hinj
  simpa [posIndex, Module.finrank_fintype_fun_eq_card] using hle

end Zeta23Core

