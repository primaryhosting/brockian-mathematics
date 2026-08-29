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
