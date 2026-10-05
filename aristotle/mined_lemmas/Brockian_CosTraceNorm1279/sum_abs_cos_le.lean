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

theorem sum_abs_cos_le (θ : ℕ → ℝ) : ∀ n : ℕ,
    ∑ k ∈ Finset.range n, |Real.cos (θ k)| ≤ (n : ℝ) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      calc (∑ k ∈ Finset.range n, |Real.cos (θ k)|) + |Real.cos (θ n)|
          ≤ (n : ℝ) + 1 := add_le_add ih (Real.abs_cos_le_one _)
        _ = ((n + 1 : ℕ) : ℝ) := by push_cast; ring

/-- **Cos Trace Norm 1279.**

For any phases `θ : Fin n → ℝ` and the diagonal matrix `D` with entries `cos (θ i)`:

* the trace norm of `D` is at most `n`;
* the absolute trace of `D` is dominated by its trace norm;
* hence the absolute trace of `D` is at most `n`;
* and both bounds are attained by the identity matrix (all phases zero). -/
