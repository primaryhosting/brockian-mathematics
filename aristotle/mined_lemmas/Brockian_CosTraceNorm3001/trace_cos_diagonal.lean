/-
/-!
# Cos Trace Norm 3001
Category: Brockian Corpus
Target: Brockian.CosTraceNorm3001
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/

import Mathlib

namespace Brockian

open Finset

/-- The trace of a diagonal matrix of cosines is the sum of those cosines. -/

lemma trace_cos_diagonal {n : ℕ} (θ : Fin n → ℝ) :
    (Matrix.diagonal fun i => Real.cos (θ i)).trace = ∑ i, Real.cos (θ i) := by
  simp [Matrix.trace_diagonal]

/-- Each cosine sum is bounded in absolute value by the number of terms. -/
