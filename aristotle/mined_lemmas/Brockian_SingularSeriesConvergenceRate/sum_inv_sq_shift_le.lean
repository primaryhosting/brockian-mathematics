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

lemma sum_inv_sq_shift_le (Q : ℕ) (hQ : 1 ≤ Q) (N : ℕ) :
    ∑ i ∈ Finset.range N, (1:ℝ) / ((i : ℝ) + Q + 1) ^ 2 ≤ 1 / (Q : ℝ) - 1 / ((Q : ℝ) + N) := by
  have hQ0 : (0:ℝ) < Q := by exact_mod_cast hQ
  induction N with
  | zero => simp
  | succ N ih =>
      have hN0 : (0:ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
      have h1 : (0:ℝ) < (Q : ℝ) + N := by linarith
      have h2 : (0:ℝ) < (Q : ℝ) + N + 1 := by linarith
      have key : (1:ℝ) / ((N : ℝ) + Q + 1) ^ 2
          ≤ 1 / ((Q : ℝ) + N) - 1 / ((Q : ℝ) + N + 1) := by
        rw [div_sub_div _ _ (ne_of_gt h1) (ne_of_gt h2),
          div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [sq_nonneg ((N : ℝ) + Q)]
      rw [Finset.sum_range_succ]
      push_cast
      calc ∑ i ∈ Finset.range N, (1:ℝ) / ((i : ℝ) + Q + 1) ^ 2 + 1 / ((N : ℝ) + Q + 1) ^ 2
          ≤ (1 / (Q : ℝ) - 1 / ((Q : ℝ) + N)) + (1 / ((Q : ℝ) + N) - 1 / ((Q : ℝ) + N + 1)) := by
            exact add_le_add ih key
        _ = 1 / (Q : ℝ) - 1 / ((Q : ℝ) + (N + 1)) := by ring_nf
      
/-- **Effective convergence rate for a singular series.**

If the local densities `a q` obey the square-root-cancellation style bound
`|a q| ≤ C / q ^ 2` for all `q ≥ 1`, then the singular series converges, and its
truncation at `Q` differs from the full series by at most `C / Q`. -/
