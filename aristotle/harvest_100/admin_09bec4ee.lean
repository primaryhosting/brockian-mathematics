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

/-- The positive index of inertia of a Hermitian matrix: the number of indices `i` such that
the `i`-th eigenvalue is positive (i.e. the number of positive eigenvalues, counted with
multiplicity). -/
noncomputable def posIndex {A : Matrix n n 𝕜} (hA : A.IsHermitian) : ℕ :=
  Fintype.card {i : n // 0 < hA.eigenvalues i}

/-- Diagonalization of the Hermitian quadratic form `x ↦ Re (xᴴ A x)`: in the eigenbasis
coordinates `y = Uᴴ x` it becomes `∑ i, μ i * ‖y i‖ ^ 2`, where `μ` are the eigenvalues. -/
lemma quadForm_eq_sum {A : Matrix n n 𝕜} (hA : A.IsHermitian) (x : n → 𝕜) :
    RCLike.re (star x ⬝ᵥ (A *ᵥ x)) =
      ∑ i, hA.eigenvalues i *
        ‖(star (hA.eigenvectorUnitary : Matrix n n 𝕜) *ᵥ x) i‖ ^ 2 := by
  set U : Matrix n n 𝕜 := (hA.eigenvectorUnitary : Matrix n n 𝕜) with hUdef
  set y : n → 𝕜 := star U *ᵥ x with hy
  have hD : star U * A * U = diagonal (RCLike.ofReal ∘ hA.eigenvalues) := by
    rw [← hA.conjStarAlgAut_star_eigenvectorUnitary]
    simp [hUdef]
  have hUs : U * star U = 1 := Unitary.coe_mul_star_self _
  have hstar : (star U)ᴴ = U := by simp [Matrix.star_eq_conjTranspose]
  have key : star x ⬝ᵥ (A *ᵥ x)
      = star y ⬝ᵥ (diagonal (RCLike.ofReal ∘ hA.eigenvalues) *ᵥ y) := by
    rw [hy, ← hD, star_mulVec, mulVec_mulVec, hstar, mul_assoc (star U * A) U (star U), hUs,
      mul_one, dotProduct_mulVec (star x ᵥ* U), vecMul_vecMul, ← mul_assoc, hUs, one_mul,
      ← dotProduct_mulVec]
  rw [key]
  simp only [dotProduct, mulVec_diagonal, map_sum, Pi.star_apply, RCLike.star_def,
    Function.comp_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show (starRingEnd 𝕜) (y i) * ((hA.eigenvalues i : 𝕜) * y i)
      = ((hA.eigenvalues i : 𝕜)) * ((starRingEnd 𝕜) (y i) * y i) by ring,
    RCLike.conj_mul, ← RCLike.ofReal_pow, ← RCLike.ofReal_mul, RCLike.ofReal_re]

/-- The coordinate map onto the positive-eigenvalue coordinates of the eigenbasis. -/
noncomputable def posCoords {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    (n → 𝕜) →ₗ[𝕜] ({i : n // 0 < hA.eigenvalues i} → 𝕜) :=
  (LinearMap.funLeft 𝕜 𝕜 (Subtype.val : {i : n // 0 < hA.eigenvalues i} → n)).comp
    (Matrix.mulVecLin (star (hA.eigenvectorUnitary : Matrix n n 𝕜)))

@[simp]
lemma posCoords_apply {A : Matrix n n 𝕜} (hA : A.IsHermitian) (x : n → 𝕜)
    (i : {i : n // 0 < hA.eigenvalues i}) :
    posCoords hA x i = (star (hA.eigenvectorUnitary : Matrix n n 𝕜) *ᵥ x) i.1 := rfl

/-- **Sylvester's law of inertia**, hard direction: if the Hermitian form associated with a
Hermitian matrix `A` is positive definite on a submodule `W` of `n → 𝕜`, then the dimension of
`W` is at most the number of positive eigenvalues of `A`. -/
theorem sylvester_finrank_le_posIndex {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (W : Submodule 𝕜 (n → 𝕜))
    (hpos : ∀ x ∈ W, x ≠ 0 → 0 < RCLike.re (star x ⬝ᵥ (A *ᵥ x))) :
    Module.finrank 𝕜 W ≤ posIndex hA := by
  set f : W →ₗ[𝕜] ({i : n // 0 < hA.eigenvalues i} → 𝕜) := (posCoords hA).comp W.subtype with hf
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    by_contra hne
    have hw0 : (w : n → 𝕜) ≠ 0 := fun h => hne (Subtype.ext h)
    have hpos' := hpos (w : n → 𝕜) w.2 hw0
    rw [quadForm_eq_sum hA] at hpos'
    have hle : ∑ i, hA.eigenvalues i *
        ‖(star (hA.eigenvectorUnitary : Matrix n n 𝕜) *ᵥ (w : n → 𝕜)) i‖ ^ 2 ≤ 0 := by
      refine Finset.sum_nonpos fun i _ => ?_
      rcases lt_or_ge 0 (hA.eigenvalues i) with hgt | hle'
      · have : (star (hA.eigenvectorUnitary : Matrix n n 𝕜) *ᵥ (w : n → 𝕜)) i = 0 := by
          have := congrFun hw ⟨i, hgt⟩
          simpa [hf] using this
        simp [this]
      · exact mul_nonpos_of_nonpos_of_nonneg hle' (by positivity)
    exact absurd hpos' (not_lt.mpr hle)
  calc Module.finrank 𝕜 W
      ≤ Module.finrank 𝕜 ({i : n // 0 < hA.eigenvalues i} → 𝕜) :=
        f.finrank_le_finrank_of_injective hinj
    _ = posIndex hA := by simp [posIndex]

end Zeta23Core

