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

lemma trace_cosDiag (θ : Fin n → ℝ) :
    Matrix.trace (cosDiag θ) = ((∑ i, Real.cos (θ i) : ℝ) : ℂ) := by
  simp [cosDiag, Matrix.trace_diagonal]

/-- Unitary invariance of the trace of the cosine matrix. -/
