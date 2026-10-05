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
