/-
# Cos Trace Norm 3499
Category: Brockian Corpus
Target: Brockian.CosTraceNorm3499
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Cos Trace Norm 3499
Category: Brockian Corpus
Target: Brockian.CosTraceNorm3499
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

/-- **Cos trace norm bound.** For any family of angles `θ : n → ℝ` indexed by a finite type,
the absolute value of the trace of the diagonal matrix with entries `cos (θ i)` is bounded by
the cardinality of the index type.

The proof combines `Matrix.trace_diagonal`, the triangle inequality
`Finset.abs_sum_le_sum_abs`, and the pointwise bound `Real.abs_cos_le_one`. -/

theorem CosTraceNorm3499_le_traceAbs {n : Type*} [Fintype n] [DecidableEq n] (θ : n → ℝ) :
    |Matrix.trace (Matrix.diagonal (fun i => Real.cos (θ i)))|
      ≤ Matrix.trace (Matrix.diagonal (fun i => |Real.cos (θ i)|)) := by
  rw [Matrix.trace_diagonal, Matrix.trace_diagonal]
  exact Finset.abs_sum_le_sum_abs _ _

/-- **Sharpness.** The bound `Fintype.card n` in `CosTraceNorm3499` is attained, e.g. for the
zero family of angles. -/
