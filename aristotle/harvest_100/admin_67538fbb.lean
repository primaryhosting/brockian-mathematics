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

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n 𝕜}

/-- The positive index of inertia `n₊(A)` of a Hermitian matrix `A`: the number of indices `i`
such that the `i`-th eigenvalue of `A` is positive. -/
noncomputable def posIndex (hA : A.IsHermitian) : ℕ :=
  Fintype.card {i : n // 0 < hA.eigenvalues i}

/-- Diagonalization of the Hermitian quadratic form `x ↦ Re (xᴴ A x)` in the eigenbasis:
it equals `∑ i, λ i * ‖y i‖ ^ 2` where `y = Uᴴ x` are the coordinates of `x` with respect to
the orthonormal eigenbasis of `A`. -/
theorem re_dotProduct_mulVec_eq_sum (hA : A.IsHermitian) (x : n → 𝕜) :
    RCLike.re (star x ⬝ᵥ (A *ᵥ x))
      = ∑ i, hA.eigenvalues i * ‖(star (hA.eigenvectorUnitary : Matrix n n 𝕜) *ᵥ x) i‖ ^ 2 := by
  set U : Matrix n n 𝕜 := (hA.eigenvectorUnitary : Matrix n n 𝕜) with hU
  set y : n → 𝕜 := star U *ᵥ x with hy
  have hUy : U *ᵥ y = x := by
    rw [hy, mulVec_mulVec]
    have hUU : U * star U = 1 := Matrix.mem_unitaryGroup_iff.mp hA.eigenvectorUnitary.2
    rw [hUU, one_mulVec]
  have hD : Uᴴ * A * U = diagonal (RCLike.ofReal ∘ hA.eigenvalues) := by
    have h := hA.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_star_apply] at h
    simpa [hU, Matrix.conjTranspose] using h
  have key : star x ⬝ᵥ (A *ᵥ x) = star y ⬝ᵥ ((diagonal (RCLike.ofReal ∘ hA.eigenvalues)) *ᵥ y) := by
    conv_lhs => rw [← hUy]
    rw [star_mulVec, mulVec_mulVec, ← dotProduct_mulVec, mulVec_mulVec, ← Matrix.mul_assoc, hD]
  rw [key, dotProduct, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hterm : star y i * (diagonal (RCLike.ofReal ∘ hA.eigenvalues) *ᵥ y) i
      = ((hA.eigenvalues i * ‖y i‖ ^ 2 : ℝ) : 𝕜) := by
    simp only [mulVec_diagonal, Pi.star_apply, RCLike.star_def, Function.comp_apply]
    rw [show (starRingEnd 𝕜) (y i) * ((hA.eigenvalues i : 𝕜) * y i)
        = (hA.eigenvalues i : 𝕜) * ((starRingEnd 𝕜) (y i) * y i) by ring, RCLike.conj_mul]
    push_cast
    ring
  rw [hterm, RCLike.ofReal_re]

/-- **Sylvester's law of inertia**, hard direction: if the Hermitian form associated with a
Hermitian matrix `A` is positive definite on a subspace `W` of `n → 𝕜`, then the dimension of `W`
is at most the positive index of inertia `posIndex A`, i.e. the number of positive eigenvalues
of `A`. -/
theorem sylvester_finrank_le_posIndex (hA : A.IsHermitian) (W : Submodule 𝕜 (n → 𝕜))
    (hW : ∀ x ∈ W, x ≠ 0 → 0 < RCLike.re (star x ⬝ᵥ (A *ᵥ x))) :
    Module.finrank 𝕜 W ≤ posIndex hA := by
  set U : Matrix n n 𝕜 := (hA.eigenvectorUnitary : Matrix n n 𝕜) with hU
  -- the linear map sending `x ∈ W` to the coordinates of `x` in the eigenbasis, restricted to
  -- the indices with positive eigenvalue
  set f : W →ₗ[𝕜] ({i : n // 0 < hA.eigenvalues i} → 𝕜) :=
    (LinearMap.funLeft 𝕜 𝕜 (Subtype.val : {i : n // 0 < hA.eigenvalues i} → n)).comp
      ((Matrix.mulVecLin (star U)).comp W.subtype) with hf
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    rintro ⟨x, hxW⟩ hx
    rw [LinearMap.mem_ker] at hx
    have hzero : ∀ i : n, 0 < hA.eigenvalues i → (star U *ᵥ x) i = 0 := by
      intro i hi
      have := congrFun hx ⟨i, hi⟩
      simpa [hf, LinearMap.funLeft_apply] using this
    have hle : RCLike.re (star x ⬝ᵥ (A *ᵥ x)) ≤ 0 := by
      rw [re_dotProduct_mulVec_eq_sum hA x]
      refine Finset.sum_nonpos fun i _ => ?_
      rcases lt_or_ge 0 (hA.eigenvalues i) with hi | hi
      · rw [hzero i hi]
        simp
      · exact mul_nonpos_of_nonpos_of_nonneg hi (by positivity)
    have hx0 : x = 0 := by
      by_contra hne
      exact absurd hle (not_le.2 (hW x hxW hne))
    simpa [Submodule.mem_bot, Subtype.ext_iff] using hx0
  have := LinearMap.finrank_le_finrank_of_injective (f := f) hinj
  rwa [Module.finrank_pi] at this

end Zeta23Core

