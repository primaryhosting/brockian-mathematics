/-
# Cos Trace Norm 3001
Category: Brockian Corpus
Target: Brockian.CosTraceNorm3001
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian

open Matrix Finset

variable {n : ℕ}

/-- The "cosine matrix" attached to a list of phases `θ : Fin n → ℝ`:
the diagonal complex matrix with entries `cos (θ i)`. -/

lemma trace_unitary_conj_cosDiag (θ : Fin n → ℝ) (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U * Uᴴ = 1) :
    Matrix.trace (U * cosDiag θ * Uᴴ) = Matrix.trace (cosDiag θ) := by
  have hU' : Uᴴ * U = 1 := mul_eq_one_comm.mp hU
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, hU', Matrix.mul_one]

/-- The trace norm of the cosine matrix is at most the dimension. -/
