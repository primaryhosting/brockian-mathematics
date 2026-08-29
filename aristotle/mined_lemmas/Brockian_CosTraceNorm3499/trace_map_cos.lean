/-
# Cos Trace Norm 3499
Category: Brockian Corpus
Target: Brockian.CosTraceNorm3499
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Real Matrix

namespace Brockian

/-- The entrywise cosine of a real matrix has trace equal to the sum of the cosines of the
diagonal entries. -/

lemma trace_map_cos {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    (A.map Real.cos).trace = ∑ i, Real.cos (A i i) := by
  simp [Matrix.trace, Matrix.diag]

/-- Each summand of the cosine trace is bounded by `1`. -/
