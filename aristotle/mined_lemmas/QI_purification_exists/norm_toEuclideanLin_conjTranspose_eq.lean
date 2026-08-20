/-
/-!
# Purification Exists
Category: Frontier Qi
Target: QI.purification_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to be the first command, so the mandated header above is kept as a
-- plain comment and repeated as the module docstring below.)
-/

import Mathlib

/-!
# Purification Exists
Category: Frontier Qi
Target: QI.purification_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ComplexOrder
open scoped MatrixOrder

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

open Matrix

section Defs

variable {n m : Type*}

/-- The matrix `n × m` representation of a vector `ψ` of the tensor product `H ⊗ K`,
where `H` has orthonormal basis indexed by `n` and `K` has orthonormal basis indexed by `m`. -/

theorem norm_toEuclideanLin_conjTranspose_eq {n m : Type*} [Fintype n] [DecidableEq n]
    [Fintype m] (A B : Matrix n m ℂ) (h : A * Aᴴ = B * Bᴴ) (x : EuclideanSpace ℂ n) :
    ‖Matrix.toEuclideanLin Aᴴ x‖ = ‖Matrix.toEuclideanLin Bᴴ x‖ := by
  have key : ∀ C : Matrix n m ℂ,
      (inner ℂ (Matrix.toEuclideanLin Cᴴ x) (Matrix.toEuclideanLin Cᴴ x) : ℂ)
        = star (x.ofLp) ᵥ* (C * Cᴴ) ⬝ᵥ x.ofLp := by
    intro C
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [Matrix.toLpLin_apply, WithLp.ofLp_toLp]
    rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose, dotProduct_comm,
      dotProduct_mulVec, Matrix.vecMul_vecMul]
  have h1 : (inner ℂ (Matrix.toEuclideanLin Aᴴ x) (Matrix.toEuclideanLin Aᴴ x) : ℂ)
      = inner ℂ (Matrix.toEuclideanLin Bᴴ x) (Matrix.toEuclideanLin Bᴴ x) := by
    rw [key A, key B, h]
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h1
  have h2 : ‖Matrix.toEuclideanLin Aᴴ x‖ ^ 2 = ‖Matrix.toEuclideanLin Bᴴ x‖ ^ 2 := by
    exact_mod_cast h1
  have h3 := congrArg Real.sqrt h2
  simpa [Real.sqrt_sq (norm_nonneg _)] using h3

/-- **Uniqueness of purifications up to an isometry on the ancilla**, in matrix form:
if `A Aᴴ = B Bᴴ` then `B = A U` for some unitary `U` acting on the ancilla index. -/
