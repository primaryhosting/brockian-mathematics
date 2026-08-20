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

lemma tsum_inv_sq_tail_le (Q : ℕ) (hQ : 1 ≤ Q) :
    ∑' i : ℕ, (1 : ℝ) / ((i : ℝ) + Q + 1) ^ 2 ≤ 1 / (Q : ℝ) := by
  refine Real.tsum_le_of_sum_range_le (fun i => by positivity) (fun n => ?_)
  have h := sum_range_inv_sq_shift_le Q hQ n
  have hpos : (0 : ℝ) ≤ 1 / ((Q : ℝ) + n) := by positivity
  linarith

/-- The comparison series `∑ C/q²` is summable (the `q = 0` term being `0`). -/
