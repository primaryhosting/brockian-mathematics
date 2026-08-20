/-!
# Erdos Discrepancy
Category: Frontier — Prime Numbers
Target: Frontier.erdos_discrepancy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

The Erdős discrepancy problem (solved by T. Tao, 2015) asserts that every `±1` sequence
`f : ℕ → ℤ` has *unbounded* discrepancy along homogeneous arithmetic progressions: the
partial sums `∑_{i=1}^{n} f (i * d)` are unbounded in absolute value as `n, d` range over
the positive integers.

A search of Mathlib turns up no formalization of the Erdős discrepancy problem (nor of the
logarithmically averaged Chowla/Elliott conjectures used in Tao's proof), and no existing

theorem apSum_eq_sum_Icc (f : ℕ → ℤ) (d n : ℕ) :
    apSum f d n = ∑ i ∈ Finset.Icc 1 n, f (i * d) := by
  induction n with
  | zero => simp [apSum]
  | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), ← ih]
      simp [apSum, List.range_succ]

/-- **Erdős discrepancy problem, base case `C = 1`** (Mathlib phrasing).
For every `±1` sequence `f` there are `d, n ≥ 1` with `|∑_{i=1}^{n} f (i * d)| > 1`. -/
