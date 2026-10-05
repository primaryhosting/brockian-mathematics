import Mathlib
/-!
# Cos Trace Norm 3001
Category: Brockian Corpus
Target: Brockian.CosTraceNorm3001
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

open Finset Matrix

/-- The trace norm (Schatten 1-norm) of a real symmetric matrix: the sum of the absolute
values of its eigenvalues, which for a symmetric matrix coincides with the sum of its
singular values. -/

theorem CosTraceNorm3001 (n : ℕ) (θ : Fin n → ℝ) :
    |(Matrix.diagonal fun i => Real.cos (θ i)).trace| ≤ ∑ i, |Real.cos (θ i)| ∧
      ∑ i, |Real.cos (θ i)| ≤ (n : ℝ) := by
  constructor
  · rw [Matrix.trace_diagonal]
    exact Finset.abs_sum_le_sum_abs _ _
  · calc ∑ i, |Real.cos (θ i)| ≤ ∑ _i : Fin n, (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => Real.abs_cos_le_one (θ i)
    _ = (n : ℝ) := by simp

/-- **Cos Trace Norm 3001, symmetric-matrix form.**
If a real symmetric `n × n` matrix `A` has eigenvalues of the form `cos (θ i)`, then
`|trace A|` is bounded by the trace norm of `A`, and that trace norm is at most `n`. -/
