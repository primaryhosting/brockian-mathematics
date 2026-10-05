import Mathlib
/-!
# Cos Trace Norm 1279
Category: Brockian Corpus
Target: Brockian.CosTraceNorm1279
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

open Finset

/-- The trace norm (Schatten 1-norm) of a real diagonal matrix: the sum of the
absolute values of its diagonal entries, which are exactly its singular values. -/

noncomputable def diagTraceNorm {n : ℕ} (d : Fin n → ℝ) : ℝ := ∑ i, |d i|

/-- Auxiliary bound, proved by induction on `n`: a sum of `n` values `|cos θ|` is at
most `n`. -/
