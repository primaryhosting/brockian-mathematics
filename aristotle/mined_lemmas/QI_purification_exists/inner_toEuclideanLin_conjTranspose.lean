/-
# Purification Exists
Category: Frontier Qi
Target: QI.purification_exists
Statement: Every mixed state has a purification, unique up to isometry on the ancilla.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Purification Exists
Category: Frontier Qi
Target: QI.purification_exists
Statement: Every mixed state has a purification, unique up to isometry on the ancilla.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

A mixed state on `ℂ^n` is modelled by a density matrix `rho : Matrix n n ℂ`, i.e. a positive
semidefinite matrix of unit trace.  A vector of the composite system `ℂ^n ⊗ ℂ^m` is modelled by
a matrix `M : Matrix n m ℂ` (its matrix of coefficients in the product basis), the squared
Hilbert–Schmidt norm `∑ i j, ‖M i j‖ ^ 2` being its squared norm as a vector, and its partial
trace over the ancilla `ℂ^m` being `M * Mᴴ`.

The main result `QI.purification_exists` states that every mixed state `rho` has a purification
by a unit vector of `ℂ^n ⊗ ℂ^n`, and that any two purifications with the same ancilla differ by
a unitary acting on the ancilla only.
-/

open scoped BigOperators
open scoped ComplexConjugate
open scoped ComplexOrder
open scoped MatrixOrder

namespace QI

open Matrix

/-- A *mixed state* (density matrix) on the finite-dimensional Hilbert space `ℂ^n`:
a positive semidefinite matrix of unit trace. -/

lemma inner_toEuclideanLin_conjTranspose (M : Matrix n m ℂ) (x y : EuclideanSpace ℂ n) :
    inner ℂ (Matrix.toEuclideanLin Mᴴ x) (Matrix.toEuclideanLin Mᴴ y)
      = inner ℂ x (Matrix.toEuclideanLin (M * Mᴴ) y) := by
  have key : (star (Mᴴ *ᵥ x.ofLp)) ⬝ᵥ (Mᴴ *ᵥ y.ofLp) = (star x.ofLp) ⬝ᵥ ((M * Mᴴ) *ᵥ y.ofLp) := by
    rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose, ← Matrix.mulVec_mulVec,
      ← Matrix.dotProduct_mulVec]
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
  have h1 : ((toEuclideanLin Mᴴ) y).ofLp = Mᴴ *ᵥ y.ofLp := rfl
  have h2 : ((toEuclideanLin Mᴴ) x).ofLp = Mᴴ *ᵥ x.ofLp := rfl
  have h3 : ((toEuclideanLin (M * Mᴴ)) y).ofLp = (M * Mᴴ) *ᵥ y.ofLp := rfl
  rw [h1, h2, h3, dotProduct_comm, key, dotProduct_comm]

/-- A linear map between finite-dimensional inner product spaces can be transported onto another
one with the same norms by a global linear isometry of the target. -/
