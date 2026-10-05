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

lemma abs_sum_cos_le {n : ℕ} (θ : Fin n → ℝ) :
    |∑ i, Real.cos (θ i)| ≤ (n : ℝ) := by
  have h : |∑ i, Real.cos (θ i)| ≤ ∑ _i : Fin n, (1 : ℝ) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine Finset.sum_le_sum fun i _ => ?_
    exact abs_le.2 ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  simpa using h

/-- Quadratic (second-order) lower bound for the cosine sum. -/
