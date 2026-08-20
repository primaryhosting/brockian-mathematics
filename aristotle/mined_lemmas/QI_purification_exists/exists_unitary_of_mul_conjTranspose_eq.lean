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

theorem exists_unitary_of_mul_conjTranspose_eq (M N : Matrix n m ℂ) (h : M * Mᴴ = N * Nᴴ) :
    ∃ W : Matrix m m ℂ, W ∈ Matrix.unitaryGroup m ℂ ∧ N = M * W := by
  set f : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ m := Matrix.toEuclideanLin Mᴴ with hf
  set g : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ m := Matrix.toEuclideanLin Nᴴ with hg
  -- the two maps have the same norms, since `M Mᴴ = N Nᴴ`
  have hnorm : ∀ x, ‖f x‖ = ‖g x‖ := by
    intro x
    have h1 := inner_toEuclideanLin_conjTranspose M x x
    have h2 := inner_toEuclideanLin_conjTranspose N x x
    rw [h] at h1
    have hinner : (inner ℂ (f x) (f x) : ℂ) = inner ℂ (g x) (g x) := by rw [hf, hg, h1, h2]
    rw [@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ, hinner]
  -- so they are intertwined by a linear isometry of the ancilla space
  obtain ⟨U, hU⟩ := exists_linearIsometry_comp_eq f g hnorm
  set b := EuclideanSpace.basisFun m ℂ with hb
  refine ⟨(LinearMap.toMatrix b.toBasis b.toBasis U.toLinearMap)ᴴ, ?_, ?_⟩
  · rw [← Matrix.star_eq_conjTranspose]
    exact Unitary.star_mem (toMatrix_linearIsometry_mem_unitaryGroup U)
  · set W := LinearMap.toMatrix b.toBasis b.toBasis U.toLinearMap with hW
    have hWlin : Matrix.toEuclideanLin W = U.toLinearMap := by
      rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, hW]
      exact Matrix.toLin_toMatrix _ _ _
    have hmul : Matrix.toEuclideanLin (W * Mᴴ)
        = (Matrix.toEuclideanLin W).comp (Matrix.toEuclideanLin Mᴴ) := by
      ext x i
      simp [Matrix.mulVec_mulVec]
    have heq : W * Mᴴ = Nᴴ := by
      apply Matrix.toEuclideanLin.injective
      rw [hmul, hWlin]
      ext x i
      exact congrArg (fun v : EuclideanSpace ℂ m => v.ofLp i) (hU x)
    have := congrArg Matrix.conjTranspose heq
    simpa [Matrix.conjTranspose_mul] using this.symm

omit [DecidableEq n] [DecidableEq m] in
/-- The trace of `M * Mᴴ` is the squared Hilbert–Schmidt (Frobenius) norm of `M`. -/
