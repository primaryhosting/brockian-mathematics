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

noncomputable def cosDiag (θ : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal fun i => (Real.cos (θ i) : ℂ)

/-- The trace norm (Schatten 1-norm) of the diagonal cosine matrix: the sum of the
absolute values of its diagonal entries, which are exactly its singular values. -/
