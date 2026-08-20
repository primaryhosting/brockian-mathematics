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

lemma toMatrix_linearIsometry_mem_unitaryGroup
    (U : EuclideanSpace ℂ m →ₗᵢ[ℂ] EuclideanSpace ℂ m) :
    (LinearMap.toMatrix (EuclideanSpace.basisFun m ℂ).toBasis (EuclideanSpace.basisFun m ℂ).toBasis
      U.toLinearMap) ∈ Matrix.unitaryGroup m ℂ := by
  set b := EuclideanSpace.basisFun m ℂ with hb
  set W := LinearMap.toMatrix b.toBasis b.toBasis U.toLinearMap with hW
  have hentry : ∀ i j, W i j = inner ℂ (b i) (U (b j)) := by
    intro i j
    rw [hW, LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      OrthonormalBasis.repr_apply_apply, OrthonormalBasis.coe_toBasis]
    rfl
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  rw [Matrix.star_eq_conjTranspose]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hentry, Matrix.one_apply]
  have hstep : ∀ k, star (inner ℂ (b k) (U (b i))) * inner ℂ (b k) (U (b j))
      = inner ℂ (U (b i)) (b k) * inner ℂ (b k) (U (b j)) := by
    intro k; rw [← inner_conj_symm (U (b i)) (b k)]; rfl
  simp only [hstep]
  rw [OrthonormalBasis.sum_inner_mul_inner, LinearIsometry.inner_map_map,
    orthonormal_iff_ite.mp b.orthonormal i j]

/-- **Unitary freedom.** If two matrices with the same index types satisfy `M * Mᴴ = N * Nᴴ`,
then they differ by a unitary acting on the column index: `N = M * W`. -/
