import Mathlib

/-!
# Uhlmann Fidelity
Category: Frontier Qi
Target: QI.uhlmann_fidelity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix Finset
open scoped MatrixOrder ComplexOrder

namespace QI

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### The dictionary between vectors of `H ⊗ H` and matrices

We model the Hilbert space `H` of a finite quantum system by `EuclideanSpace ℂ n` and the
composite system `H ⊗ H` by `EuclideanSpace ℂ (n × n)`.  A vector of the composite system is
the same thing as a matrix of coefficients. -/

/-- The matrix of coefficients of a vector of `H ⊗ H = EuclideanSpace ℂ (n × n)`. -/

lemma reducedState_eq (ψ : EuclideanSpace ℂ (n × n)) :
    reducedState ψ = matrixOfVec ψ * (matrixOfVec ψ)ᴴ := by
  ext i i'
  simp [reducedState, matrixOfVec, Matrix.mul_apply, Matrix.conjTranspose_apply]

omit [DecidableEq n] in
