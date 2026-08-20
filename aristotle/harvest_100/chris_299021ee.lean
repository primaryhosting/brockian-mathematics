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

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The positive index of inertia `n₊(A)` of a Hermitian matrix `A`: the number of indices `i`
for which the `i`-th eigenvalue of `A` is positive. -/
noncomputable def posIndex {A : Matrix n n 𝕜} (hA : A.IsHermitian) : ℕ :=
  Fintype.card {i : n // 0 < hA.eigenvalues i}

/-- Diagonalization of the Hermitian quadratic form `x ↦ Re (xᴴ A x)`: in the coordinates
`y = Uᴴ x` given by the eigenvector unitary `U` of `A`, the form is
`∑ i, λ i * ‖y i‖ ^ 2`, where `λ` are the eigenvalues of `A`. -/
theorem re_dotProduct_mulVec_eq_sum {A : Matrix n n 𝕜} (hA : A.IsHermitian) (x : n → 𝕜) :
    RCLike.re (star x ⬝ᵥ (A *ᵥ x)) =
      ∑ i, hA.eigenvalues i * ‖(star (hA.eigenvectorUnitary : Matrix n n 𝕜) *ᵥ x) i‖ ^ 2 := by
  set U : Matrix n n 𝕜 := (hA.eigenvectorUnitary : Matrix n n 𝕜) with hU
  set y : n → 𝕜 := star U *ᵥ x with hy
  have hAx : A *ᵥ x = U *ᵥ ((diagonal (RCLike.ofReal ∘ hA.eigenvalues)) *ᵥ y) := by
    conv_lhs => rw [hA.spectral_theorem]
    simp [Unitary.conjStarAlgAut_apply, ← mulVec_mulVec, hy, hU]
  have hstar : star x ᵥ* U = star y := by
    rw [hy, star_mulVec, Matrix.star_eq_conjTranspose, conjTranspose_conjTranspose]
  rw [hAx, dotProduct_mulVec, hstar, dotProduct]
  simp only [mulVec_diagonal, Pi.star_apply, Function.comp_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show (star (y i) * ((hA.eigenvalues i : 𝕜) * y i))
      = (hA.eigenvalues i : 𝕜) * (star (y i) * y i) by ring, RCLike.star_def, RCLike.conj_mul]
  simp

/-- **Sylvester's law of inertia**, hard direction: if the Hermitian form associated with a
Hermitian matrix `A` is positive definite on a subspace `W` of `n → 𝕜`, then
`dim W ≤ n₊(A)`, the number of positive eigenvalues of `A`. -/
theorem sylvester_finrank_le_posIndex {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (W : Submodule 𝕜 (n → 𝕜))
    (hW : ∀ x ∈ W, x ≠ 0 → 0 < RCLike.re (star x ⬝ᵥ (A *ᵥ x))) :
    Module.finrank 𝕜 W ≤ posIndex hA := by
  set U : Matrix n n 𝕜 := (hA.eigenvectorUnitary : Matrix n n 𝕜) with hU
  -- The linear map sending `x` to the coordinates of `Uᴴ x` at the positive eigenvalues.
  set f : (n → 𝕜) →ₗ[𝕜] ({i : n // 0 < hA.eigenvalues i} → 𝕜) :=
    (LinearMap.funLeft 𝕜 𝕜 (Subtype.val : {i : n // 0 < hA.eigenvalues i} → n)).comp
      (Matrix.mulVecLin (star U)) with hf
  have hinj : Function.Injective ⇑(f.comp W.subtype) := by
    rw [← LinearMap.ker_eq_bot]
    rw [Submodule.eq_bot_iff]
    rintro ⟨x, hxW⟩ hx
    rw [LinearMap.mem_ker] at hx
    have hx' : ∀ i : n, 0 < hA.eigenvalues i → (star U *ᵥ x) i = 0 := by
      intro i hi
      have := congrFun hx ⟨i, hi⟩
      simpa [hf, LinearMap.funLeft_apply, Matrix.mulVecLin_apply] using this
    -- the quadratic form is nonpositive on `x`
    have hle : RCLike.re (star x ⬝ᵥ (A *ᵥ x)) ≤ 0 := by
      rw [re_dotProduct_mulVec_eq_sum hA x]
      refine Finset.sum_nonpos fun i _ => ?_
      rcases lt_or_ge 0 (hA.eigenvalues i) with hi | hi
      · rw [← hU, hx' i hi]
        simp
      · exact mul_nonpos_of_nonpos_of_nonneg hi (by positivity)
    by_contra hne
    have hx0 : x ≠ 0 := by
      intro h
      exact hne (Subtype.ext h)
    exact absurd hle (not_le.mpr (hW x hxW hx0))
  calc Module.finrank 𝕜 W
      ≤ Module.finrank 𝕜 ({i : n // 0 < hA.eigenvalues i} → 𝕜) :=
        LinearMap.finrank_le_finrank_of_injective hinj
    _ = posIndex hA := by
        rw [Module.finrank_pi]
        exact Fintype.card_congr (Equiv.refl _)

end Zeta23Core

