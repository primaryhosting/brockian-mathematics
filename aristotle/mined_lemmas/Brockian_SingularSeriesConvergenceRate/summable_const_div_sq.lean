/-
# Singular Series Convergence Rate
Category: Brockian Corpus
Target: Brockian.SingularSeriesConvergenceRate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Finset

namespace Brockian

/-- The comparison series `q ↦ C / q ^ 2` used to control a singular series. -/

lemma summable_const_div_sq (C : ℝ) : Summable (fun q : ℕ => C / (q : ℝ) ^ 2) := by
  have h : Summable (fun q : ℕ => (1 : ℝ) / (q : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  simpa [div_eq_mul_inv, mul_comm] using h.mul_left C

/-- Tail estimate for the comparison series: for `1 ≤ N`, every partial sum of
`i ↦ C / (i + N) ^ 2` is at most `2 * C / N`. -/
