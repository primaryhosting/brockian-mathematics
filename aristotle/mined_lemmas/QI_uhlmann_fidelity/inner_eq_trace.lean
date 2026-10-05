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

lemma inner_eq_trace (ψ φ : EuclideanSpace ℂ (n × n)) :
    (inner ℂ ψ φ : ℂ) = ((matrixOfVec ψ)ᴴ * matrixOfVec φ).trace := by
  simp [PiLp.inner_apply, Matrix.trace, Matrix.mul_apply, matrixOfVec, Matrix.diag,
    Fintype.sum_prod_type, RCLike.inner_apply, mul_comm]
  rw [Finset.sum_comm]

omit [DecidableEq n] in
