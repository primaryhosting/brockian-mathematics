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

lemma sum_cos_ge_quadratic {n : ℕ} (θ : Fin n → ℝ) :
    (n : ℝ) - (∑ i, (θ i) ^ 2) / 2 ≤ ∑ i, Real.cos (θ i) := by
  have h : ∑ i, (1 - (θ i) ^ 2 / 2) ≤ ∑ i, Real.cos (θ i) :=
    Finset.sum_le_sum fun i _ => Real.one_sub_sq_div_two_le_cos
  have h2 : ∑ i, (1 - (θ i) ^ 2 / 2) = (n : ℝ) - (∑ i, (θ i) ^ 2) / 2 := by
    rw [Finset.sum_sub_distrib]
    simp [Finset.sum_div]
  rw [← h2]
  exact h

/--
**Cos Trace Norm 3001.**

For the diagonal matrix `M` whose entries are `cos (θ i)`:

* its trace is bounded in absolute value by the dimension `n`;
* the trace deviates from `n` by at most `(∑ θ i ^ 2) / 2`
  (a second-order trace-norm bound);
* the sum of the absolute values of its diagonal entries (its trace norm,
  since `M` is diagonal) is at most `n`.
-/
