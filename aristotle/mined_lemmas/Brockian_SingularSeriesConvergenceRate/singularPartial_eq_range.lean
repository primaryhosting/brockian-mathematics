import Mathlib

/-!
# Singular Series Convergence Rate
Category: Brockian Corpus
Target: Brockian.SingularSeriesConvergenceRate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Filter

namespace Brockian

/-- The truncated singular series: the partial sum `∑_{q = 1}^{Q} a q` of the local
densities `a q`. -/

lemma singularPartial_eq_range (a : ℕ → ℝ) (Q : ℕ) :
    singularPartial a Q = ∑ i ∈ Finset.range Q, a (i + 1) := by
  induction Q with
  | zero => simp [singularPartial]
  | succ Q ih =>
      rw [singularPartial, Finset.sum_Icc_succ_top (by omega), ← singularPartial, ih,
        Finset.sum_range_succ]

/-- Telescoping bound: the tail `∑_{i < N} 1/(i+Q+1)^2` is at most `1/Q - 1/(Q+N)`. -/
