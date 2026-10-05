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

lemma norm_trace_le (A B : Matrix n n ℂ) :
    ‖(Aᴴ * B).trace‖ ≤ Real.sqrt ((Aᴴ * A).trace.re) * Real.sqrt ((Bᴴ * B).trace.re) := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (vecOfMatrix A) (vecOfMatrix B)
  rwa [inner_eq_trace, matrixOfVec_vecOfMatrix, matrixOfVec_vecOfMatrix, norm_vecOfMatrix,
    norm_vecOfMatrix] at h

/-! ### Polar decomposition -/

/-- If the columns of `N` are pairwise orthogonal with norms `s j`, then `N = W * diagonal s`
for a unitary `W`. -/
