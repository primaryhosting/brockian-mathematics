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

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Zeta23Core

open Matrix

variable {𝕜 : Type*} {n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

/-- The positive index of inertia of a Hermitian matrix: the number of positive eigenvalues. -/
noncomputable def posIndex {A : Matrix n n 𝕜} (hA : A.IsHermitian) : ℕ :=
  Fintype.card {i : n // 0 < hA.eigenvalues i}

/-- Diagonalization of the quadratic form of a Hermitian matrix in the eigenvector coordinates
`y = Uᴴ x`. -/
lemma quadraticForm_eq_sum {A : Matrix n n 𝕜} (hA : A.IsHermitian) (x : n → 𝕜) :
    star x ⬝ᵥ (A *ᵥ x) = ∑ i, (hA.eigenvalues i : 𝕜) *
      (star ((star (hA.eigenvectorUnitary : Matrix n n 𝕜)) *ᵥ x) i *
        ((star (hA.eigenvectorUnitary : Matrix n n 𝕜)) *ᵥ x) i) := by
  set U := (hA.eigenvectorUnitary : Matrix n n 𝕜) with hUdef
  have hA' : A = U * diagonal (RCLike.ofReal ∘ hA.eigenvalues) * star U := by
    conv_lhs => rw [hA.spectral_theorem]
    rfl
  conv_lhs => rw [hA']
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
  have h2 : star x ᵥ* U = star ((star U) *ᵥ x) := by
    ext i; simp [Matrix.vecMul, Matrix.mulVec, dotProduct, Matrix.star_apply, mul_comm]
  rw [h2]
  simp [Matrix.mulVec_diagonal, dotProduct, mul_comm, mul_assoc, mul_left_comm]

/-- The real part of the quadratic form is the weighted sum of squared eigen-coordinates. -/
lemma re_quadraticForm_eq_sum {A : Matrix n n 𝕜} (hA : A.IsHermitian) (x : n → 𝕜) :
    RCLike.re (star x ⬝ᵥ (A *ᵥ x)) =
      ∑ i, hA.eigenvalues i * ‖((star (hA.eigenvectorUnitary : Matrix n n 𝕜)) *ᵥ x) i‖ ^ 2 := by
  rw [quadraticForm_eq_sum hA x, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (star ((star (hA.eigenvectorUnitary : Matrix n n 𝕜)) *ᵥ x)) i *
      ((star (hA.eigenvectorUnitary : Matrix n n 𝕜)) *ᵥ x) i =
      ((‖((star (hA.eigenvectorUnitary : Matrix n n 𝕜)) *ᵥ x) i‖ ^ 2 : ℝ) : 𝕜) := by
    rw [Pi.star_apply, RCLike.star_def, RCLike.conj_mul]
    norm_cast
  rw [this, ← RCLike.ofReal_mul, RCLike.ofReal_re]

/-- The `𝕜`-linear map sending a vector to the coordinates, in the eigenvector basis, that
correspond to positive eigenvalues. -/
noncomputable def posCoords {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    (n → 𝕜) →ₗ[𝕜] ({i : n // 0 < hA.eigenvalues i} → 𝕜) where
  toFun x := fun i => ((star (hA.eigenvectorUnitary : Matrix n n 𝕜)) *ᵥ x) i.1
  map_add' x y := by
    ext i; simp [Matrix.mulVec_add]
  map_smul' c x := by
    ext i; simp [Matrix.mulVec_smul]

/-- If `x` is a nonzero vector whose positive eigen-coordinates all vanish, then the quadratic
form is nonpositive at `x`. -/
lemma re_quadraticForm_nonpos_of_posCoords_eq_zero {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {x : n → 𝕜} (hx : posCoords hA x = 0) :
    RCLike.re (star x ⬝ᵥ (A *ᵥ x)) ≤ 0 := by
  rw [re_quadraticForm_eq_sum hA x]
  refine Finset.sum_nonpos fun i _ => ?_
  rcases le_or_gt (hA.eigenvalues i) 0 with h | h
  · exact mul_nonpos_of_nonpos_of_nonneg h (by positivity)
  · have : ((star (hA.eigenvectorUnitary : Matrix n n 𝕜)) *ᵥ x) i = 0 := by
      have := congrFun hx ⟨i, h⟩
      simpa [posCoords] using this
    simp [this]

/-- **Sylvester's law of inertia**, hard direction: if a Hermitian matrix `A` defines a positive
definite form on a subspace `W`, then `dim W ≤ n₊(A)`, the number of positive eigenvalues
of `A`. -/
theorem sylvester_finrank_le_posIndex {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (W : Submodule 𝕜 (n → 𝕜))
    (hW : ∀ x ∈ W, x ≠ 0 → 0 < RCLike.re (star x ⬝ᵥ (A *ᵥ x))) :
    Module.finrank 𝕜 W ≤ posIndex hA := by
  have hinj : Function.Injective ((posCoords hA).domRestrict W) := by
    rw [← LinearMap.ker_eq_bot]
    refine (Submodule.eq_bot_iff _).2 fun x hx => ?_
    by_contra hne
    have hx0 : (x : n → 𝕜) ≠ 0 := fun h => hne (Subtype.ext h)
    have h1 : posCoords hA (x : n → 𝕜) = 0 := by
      simpa [LinearMap.mem_ker] using hx
    exact absurd (re_quadraticForm_nonpos_of_posCoords_eq_zero hA h1)
      (not_le.2 (hW _ x.2 hx0))
  have := LinearMap.finrank_le_finrank_of_injective (f := (posCoords hA).domRestrict W) hinj
  simpa [posIndex, Module.finrank_pi] using this

end Zeta23Core

