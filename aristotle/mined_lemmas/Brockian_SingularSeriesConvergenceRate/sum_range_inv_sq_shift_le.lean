/-
# Singular Series Convergence Rate
Category: Brockian Corpus
Target: Brockian.SingularSeriesConvergenceRate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Singular Series Convergence Rate
Category: Brockian Corpus
Target: Brockian.SingularSeriesConvergenceRate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

open Finset

/-- Telescoping tail estimate: for `Q ≥ 1`,
`∑_{i < n} 1/(i+Q+1)^2 ≤ 1/Q - 1/(Q+n)`. -/

lemma sum_range_inv_sq_shift_le (Q : ℕ) (hQ : 1 ≤ Q) (n : ℕ) :
    ∑ i ∈ range n, (1 : ℝ) / ((i : ℝ) + Q + 1) ^ 2 ≤ 1 / (Q : ℝ) - 1 / ((Q : ℝ) + n) := by
  have hQ' : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
  induction n with
  | zero => simp
  | succ n ih =>
      have h1 : (0 : ℝ) < (Q : ℝ) + n := by positivity
      have h2 : (0 : ℝ) < (Q : ℝ) + n + 1 := by positivity
      have key : (1 : ℝ) / ((n : ℝ) + Q + 1) ^ 2 ≤ 1 / ((Q : ℝ) + n) - 1 / ((Q : ℝ) + n + 1) := by
        rw [div_sub_div _ _ (ne_of_gt h1) (ne_of_gt h2),
          div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [h1.le, h2.le]
      have hsplit : ∑ i ∈ range (n + 1), (1 : ℝ) / ((i : ℝ) + Q + 1) ^ 2
          = (∑ i ∈ range n, (1 : ℝ) / ((i : ℝ) + Q + 1) ^ 2) + 1 / ((n : ℝ) + Q + 1) ^ 2 :=
        Finset.sum_range_succ _ _
      have hcast : ((Q : ℝ) + ((n + 1 : ℕ) : ℝ)) = (Q : ℝ) + n + 1 := by push_cast; ring
      rw [hsplit, hcast]
      linarith

/-- The tail of `∑ 1/q²` beyond `Q` is at most `1/Q`. -/
