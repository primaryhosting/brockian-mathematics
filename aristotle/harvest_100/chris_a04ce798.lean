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
open scoped Classical

open Matrix Unitary

namespace Zeta23Core

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

/-- The positive index of inertia of a Hermitian matrix: the number of positive eigenvalues. -/
noncomputable def posIndex {A : Matrix n n 𝕜} (hA : A.IsHermitian) : ℕ :=
  Fintype.card {i // 0 < hA.eigenvalues i}

/-- Diagonalization in the form `A = U * D * Uᴴ`. -/
lemma spectral_mul_form {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    A = (hA.eigenvectorUnitary : Matrix n n 𝕜) * diagonal (RCLike.ofReal ∘ hA.eigenvalues) *
      star (hA.eigenvectorUnitary : Matrix n n 𝕜) := by
  conv_lhs => rw [hA.spectral_theorem, Unitary.conjStarAlgAut_apply]

/-- The quadratic form of a Hermitian matrix, in eigencoordinates. -/
lemma re_quadratic_form_eq {A : Matrix n n 𝕜} (hA : A.IsHermitian) (x : n → 𝕜) :
    RCLike.re (star x ⬝ᵥ (A *ᵥ x)) =
      ∑ i, hA.eigenvalues i * ‖(star (hA.eigenvectorUnitary : Matrix n n 𝕜) *ᵥ x) i‖ ^ 2 := by
  set U : Matrix n n 𝕜 := (hA.eigenvectorUnitary : Matrix n n 𝕜) with hU
  set y : n → 𝕜 := star U *ᵥ x with hy
  have hstar : star y = vecMul (star x) U := by
    rw [hy, star_mulVec, ← Matrix.star_eq_conjTranspose, star_star]
  have h1 : star x ⬝ᵥ (A *ᵥ x) = star y ⬝ᵥ (diagonal (RCLike.ofReal ∘ hA.eigenvalues) *ᵥ y) := by
    conv_lhs => rw [spectral_mul_form hA]
    rw [← hU, ← mulVec_mulVec, ← mulVec_mulVec, ← hy, dotProduct_mulVec, hstar]
  rw [h1, dotProduct, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : star (y i) * ((diagonal (RCLike.ofReal ∘ hA.eigenvalues) *ᵥ y) i)
      = ((hA.eigenvalues i : 𝕜)) * (star (y i) * y i) := by
    rw [mulVec_diagonal]
    simp [Function.comp]
    ring
  rw [Pi.star_apply, this, RCLike.star_def, RCLike.conj_mul, ← RCLike.ofReal_pow,
    ← RCLike.ofReal_mul, RCLike.ofReal_re]

/-- **Sylvester's law of inertia**, hard direction: if a Hermitian matrix `A` is positive
definite on a subspace `W`, then `dim W ≤ n₊(A)`, the number of positive eigenvalues of `A`. -/
theorem sylvester_finrank_le_posIndex {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (W : Submodule 𝕜 (n → 𝕜))
    (hW : ∀ x ∈ W, x ≠ 0 → 0 < RCLike.re (star x ⬝ᵥ (A *ᵥ x))) :
    Module.finrank 𝕜 W ≤ posIndex hA := by
  set U : Matrix n n 𝕜 := (hA.eigenvectorUnitary : Matrix n n 𝕜) with hU
  set P : Type _ := {i : n // 0 < hA.eigenvalues i} with hP
  let f : (n → 𝕜) →ₗ[𝕜] (P → 𝕜) :=
    (LinearMap.funLeft 𝕜 𝕜 (Subtype.val : P → n)).comp (star U).mulVecLin
  let g : W →ₗ[𝕜] (P → 𝕜) := f.comp W.subtype
  have hginj : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    rintro ⟨x, hx⟩ hker
    have hker' : ∀ i : P, (star U *ᵥ x) (i : n) = 0 := by
      intro i
      have : g ⟨x, hx⟩ = 0 := hker
      have := congrFun this i
      simpa [g, f, LinearMap.funLeft, Matrix.mulVecLin] using this
    have hle : RCLike.re (star x ⬝ᵥ (A *ᵥ x)) ≤ 0 := by
      rw [re_quadratic_form_eq hA x]
      refine Finset.sum_nonpos fun i _ => ?_
      by_cases hpos : 0 < hA.eigenvalues i
      · rw [hker' ⟨i, hpos⟩]
        simp
      · exact mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hpos) (by positivity)
    have hx0 : x = 0 := by
      by_contra hne
      exact absurd hle (not_le.mpr (hW x hx hne))
    exact Subtype.ext hx0
  have := LinearMap.finrank_le_finrank_of_injective (f := g) hginj
  simpa [posIndex, hP] using this

end Zeta23Core

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

