-- Note: Lean 4 requires `import` commands to precede any doc comment, so the requested
-- header block appears immediately below the import.
import Mathlib

/-!
# Commuting Simultaneous
Category: Quantum Physics
Target: QPhys.commuting_simultaneous
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Module Submodule Module.End Matrix

namespace QPhys

/-- Two commuting symmetric (Hermitian) operators on a finite-dimensional inner product space
have a common orthonormal eigenbasis, indexed by any index type of the right cardinality. -/

theorem conjugate_eq_diagonal_of_eigenvectors {n : Type*} [Fintype n] [DecidableEq n]
    (v : OrthonormalBasis n ℂ (EuclideanSpace ℂ n)) (M : Matrix n n ℂ) (d : n → ℂ)
    (h : ∀ j, M *ᵥ ⇑(v j) = d j • ⇑(v j)) :
    star ((EuclideanSpace.basisFun n ℂ).toBasis.toMatrix v.toBasis) * M *
      ((EuclideanSpace.basisFun n ℂ).toBasis.toMatrix v.toBasis) = Matrix.diagonal d := by
  classical
  set U := (EuclideanSpace.basisFun n ℂ).toBasis.toMatrix v.toBasis with hU
  have hUmem : U ∈ Matrix.unitaryGroup n ℂ :=
    (EuclideanSpace.basisFun n ℂ).toMatrix_orthonormalBasis_mem_unitary v
  have hcol : ∀ j, U *ᵥ (Pi.single j 1 : n → ℂ) = ⇑(v j) := by
    intro j
    rw [Matrix.mulVec_single_one]
    rfl
  have hstar : ∀ j, (star U) *ᵥ ⇑(v j) = (Pi.single j 1 : n → ℂ) := by
    intro j
    rw [← hcol, Matrix.mulVec_mulVec, (Matrix.mem_unitaryGroup_iff'.mp hUmem), Matrix.one_mulVec]
  ext i j
  have h1 : (star U * M * U) *ᵥ (Pi.single j 1 : n → ℂ)
      = Matrix.diagonal d *ᵥ (Pi.single j 1 : n → ℂ) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hcol, h j, Matrix.mulVec_smul, hstar j,
      Matrix.diagonal_mulVec_single, mul_one]
    ext k
    simp [Pi.single_apply]
  have h2 := congrFun h1 i
  rcases eq_or_ne i j with rfl | hij
  · simpa [Matrix.mulVec_single_one, Pi.single_apply, Matrix.diagonal_apply] using h2
  · simpa [Matrix.mulVec_single_one, Pi.single_apply, Matrix.diagonal_apply, hij] using h2

/-- **Commuting Hermitian operators are simultaneously diagonalizable.**

Given two commuting Hermitian matrices `A` and `B` (observables in quantum mechanics), there is a
single unitary matrix `U` and real-valued functions `a`, `b` (the eigenvalues) such that both
`U⋆ A U` and `U⋆ B U` are diagonal, with diagonal entries `a` and `b` respectively.  Equivalently,
`A` and `B` possess a common orthonormal eigenbasis, namely the columns of `U`. -/
