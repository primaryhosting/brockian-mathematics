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

lemma norm_vecOfMatrix (A : Matrix n n ℂ) : ‖vecOfMatrix A‖ = Real.sqrt ((Aᴴ * A).trace.re) := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  simp only [vecOfMatrix, Matrix.trace, Matrix.mul_apply, Matrix.diag, Fintype.sum_prod_type,
    Matrix.conjTranspose_apply, Complex.re_sum, WithLp.ofLp_toLp]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.sq_norm]
  simp [Complex.normSq_apply]

omit [DecidableEq n] in
/-- Frobenius (Hilbert–Schmidt) Cauchy–Schwarz inequality for the trace pairing. -/
