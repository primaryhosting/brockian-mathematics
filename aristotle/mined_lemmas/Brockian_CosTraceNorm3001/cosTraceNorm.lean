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

noncomputable def cosTraceNorm (θ : Fin n → ℝ) : ℝ := ∑ i, |Real.cos (θ i)|

/-- Trace of the cosine matrix. -/
