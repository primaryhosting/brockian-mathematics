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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Zeta23Core

open Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n 𝕜}

/-- The positive index (number of positive eigenvalues, with multiplicity) of a Hermitian
matrix. -/
noncomputable def posIndex (hA : A.IsHermitian) : ℕ :=
  Fintype.card {i : n // 0 < hA.eigenvalues i}

/-- Explicit unitary diagonalization `A = U * D * Uᴴ` of a Hermitian matrix. -/
theorem isHermitian_eq_unitary_mul_diagonal_mul_star (hA : A.IsHermitian) :
    A = (hA.eigenvectorUnitary : Matrix n n 𝕜) *
      diagonal (fun i => ((hA.eigenvalues i : ℝ) : 𝕜)) *
      star (hA.eigenvectorUnitary : Matrix n n 𝕜) := by
  conv_lhs => rw [hA.spectral_theorem]
  simp [Unitary.conjStarAlgAut_apply, Function.comp_def]

/-- Diagonalizing the quadratic form: if `A = U * diagonal d * Uᴴ`, then
`Re (xᴴ A x) = ∑ i, d i * ‖(Uᴴ x) i‖ ^ 2`. -/
theorem re_dotProduct_mulVec_of_diagonalization (U : Matrix n n 𝕜) (d : n → ℝ)
    (hsp : A = U * diagonal (fun i => ((d i : ℝ) : 𝕜)) * star U) (x : n → 𝕜) :
    RCLike.re (star x ⬝ᵥ (A *ᵥ x)) = ∑ i, d i * ‖(star U *ᵥ x) i‖ ^ 2 := by
  set y : n → 𝕜 := star U *ᵥ x with hy
  have h1 : star x ⬝ᵥ (A *ᵥ x)
      = star y ⬝ᵥ ((diagonal (fun i => ((d i : ℝ) : 𝕜))) *ᵥ y) := by
    rw [hsp, hy, star_mulVec]
    simp [Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, mul_assoc,
      Matrix.star_eq_conjTranspose]
  rw [h1, dotProduct, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mulVec_diagonal, Pi.star_apply]
  have h2 : star (y i) * (((d i : ℝ) : 𝕜) * y i) = ((d i * ‖y i‖ ^ 2 : ℝ) : 𝕜) := by
    push_cast
    rw [RCLike.star_def,
      show (starRingEnd 𝕜) (y i) * (↑(d i) * y i) = ↑(d i) * ((starRingEnd 𝕜) (y i) * y i) by ring,
      RCLike.conj_mul]
  rw [h2, RCLike.ofReal_re]

/-- **Sylvester's law of inertia**, hard direction: if a Hermitian form given by a Hermitian
matrix `A` is positive definite on a subspace `W`, then `dim W ≤ n₊(A)`, the number of positive
eigenvalues of `A`. -/
theorem sylvester_finrank_le_posIndex (hA : A.IsHermitian) (W : Submodule 𝕜 (n → 𝕜))
    (hW : ∀ x ∈ W, x ≠ 0 → 0 < RCLike.re (star x ⬝ᵥ (A *ᵥ x))) :
    Module.finrank 𝕜 W ≤ posIndex hA := by
  set U : Matrix n n 𝕜 := (hA.eigenvectorUnitary : Matrix n n 𝕜)
  set d : n → ℝ := hA.eigenvalues with hd
  have hsp : A = U * diagonal (fun i => ((d i : ℝ) : 𝕜)) * star U :=
    isHermitian_eq_unitary_mul_diagonal_mul_star hA
  -- the linear map sending `x` to the positive-eigenvalue coordinates of `Uᴴ x`
  set g : (n → 𝕜) →ₗ[𝕜] ({i : n // 0 < d i} → 𝕜) :=
    (LinearMap.funLeft 𝕜 𝕜 (Subtype.val : {i : n // 0 < d i} → n)).comp
      (Matrix.mulVecLin (star U)) with hg
  set f : W →ₗ[𝕜] ({i : n // 0 < d i} → 𝕜) := g.comp W.subtype with hf
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    rintro ⟨x, hxW⟩ hx
    rw [LinearMap.mem_ker] at hx
    have hxcoord : ∀ i : n, 0 < d i → (star U *ᵥ x) i = 0 := by
      intro i hi
      have := congrFun hx ⟨i, hi⟩
      simpa [hf, hg, LinearMap.funLeft_apply] using this
    have hle : RCLike.re (star x ⬝ᵥ (A *ᵥ x)) ≤ 0 := by
      rw [re_dotProduct_mulVec_of_diagonalization U d hsp x]
      refine Finset.sum_nonpos fun i _ => ?_
      rcases lt_or_ge 0 (d i) with hi | hi
      · rw [hxcoord i hi]
        simp
      · exact mul_nonpos_of_nonpos_of_nonneg hi (by positivity)
    have hx0 : x = 0 := by
      by_contra hne
      exact absurd hle (not_le.2 (hW x hxW hne))
    exact Submodule.coe_eq_zero.1 hx0
  have h1 : Module.finrank 𝕜 W ≤ Module.finrank 𝕜 ({i : n // 0 < d i} → 𝕜) :=
    LinearMap.finrank_le_finrank_of_injective hinj
  simpa [posIndex, hd] using h1

end Zeta23Core

