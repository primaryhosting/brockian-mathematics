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

theorem CosTraceNorm3499 {n : Type*} [Fintype n] [DecidableEq n] (θ : n → ℝ) :
    |Matrix.trace (Matrix.diagonal (fun i => Real.cos (θ i)))| ≤ (Fintype.card n : ℝ) := by
  rw [Matrix.trace_diagonal]
  calc |∑ i, Real.cos (θ i)|
      ≤ ∑ i, |Real.cos (θ i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : n, (1 : ℝ) := Finset.sum_le_sum fun i _ => Real.abs_cos_le_one _
    _ = (Fintype.card n : ℝ) := by simp [Finset.card_univ]

/-- **Sharper form.** The trace of the diagonal cosine matrix is bounded in absolute value by
the trace of the diagonal matrix of the absolute values `|cos (θ i)|`, i.e. by the trace norm
(sum of singular values) of that Hermitian diagonal matrix. -/
