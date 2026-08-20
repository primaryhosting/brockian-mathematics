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

lemma summable_const_div_nat_sq (C : ℝ) : Summable (fun q : ℕ => C / (q : ℝ) ^ 2) := by
  have h : Summable (fun q : ℕ => (1 : ℝ) / (q : ℝ) ^ 2) :=
    (Real.summable_one_div_nat_pow).2 (by norm_num)
  simpa [div_eq_mul_inv, mul_comm] using h.mul_left C

/--
**Singular Series Convergence Rate.**

Let `a : ℕ → ℝ` be the terms of a singular series, i.e. an arithmetic series whose
`q`-th term obeys the standard effective bound `|a q| ≤ C / q²` for `q ≥ 1` (with `a 0 = 0`).
Then the series converges, and truncating it at level `Q ≥ 1` incurs an error of at most
`C / Q` — an effective convergence rate for the singular series.
-/
