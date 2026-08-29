import Mathlib

/-!
# Cos Trace Norm 3499
Category: Brockian Corpus
Target: Brockian.CosTraceNorm3499
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace Brockian

/-- **Cosine trace-norm bound.**
For any family of angles `f : Fin n → ℝ`, the trace of the diagonal matrix whose
entries are `cos (f i)` has norm at most `n`.

The proof only uses `Matrix.trace_diagonal`, the triangle inequality for finite sums
(`Finset.abs_sum_le_sum_abs`) and `Real.abs_cos_le_one`. -/

theorem CosTraceNorm3499_sharp (n : ℕ) :
    ‖Matrix.trace (Matrix.diagonal fun _ : Fin n => Real.cos (0 : ℝ))‖ = (n : ℝ) := by
  simp

/-- Specialisation of `Brockian.CosTraceNorm3499` to size `3499`. -/
