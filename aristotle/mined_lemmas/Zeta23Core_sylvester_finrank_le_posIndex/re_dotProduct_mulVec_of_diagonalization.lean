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
