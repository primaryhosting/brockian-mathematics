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

theorem erdos_discrepancy_sum_Icc (f : ℕ → ℤ) (hf : ∀ n, 1 ≤ n → f n = 1 ∨ f n = -1) :
    ∃ d n : ℕ, 1 ≤ d ∧ 1 ≤ n ∧ 1 < |∑ i ∈ Finset.Icc 1 n, f (i * d)| := by
  obtain ⟨d, n, hd, hn, hlt⟩ := erdos_discrepancy f hf
  refine ⟨d, n, hd, hn, ?_⟩
  rw [← apSum_eq_sum_Icc, Int.abs_eq_natAbs]
  exact_mod_cast hlt

/-- The full Erdős discrepancy conjecture (Tao's theorem), in Mathlib phrasing, is
equivalent to `Frontier.ErdosDiscrepancyConjecture`. -/
