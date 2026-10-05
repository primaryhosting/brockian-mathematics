import Mathlib
/-!
# Singular Series Convergence Rate
Category: Brockian Corpus
Target: Brockian.SingularSeriesConvergenceRate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace Brockian

/-- Telescoping partial-sum estimate: for `N ≥ 1`,
`∑_{i < n} 1/(i+N)^2 ≤ 1/(N - 1/2) - 1/(N + n - 1/2)`.
Proved by induction on `n`, using `1/x^2 ≤ 1/(x - 1/2) - 1/(x + 1/2)`. -/

lemma summable_inv_sq_shift (N : ℕ) :
    Summable fun i : ℕ => (((i : ℝ) + N) ^ 2)⁻¹ := by
  have h : Summable fun n : ℕ => (((n : ℝ)) ^ 2)⁻¹ :=
    Real.summable_nat_pow_inv.2 (by norm_num)
  have h2 := (summable_nat_add_iff (f := fun n : ℕ => (((n : ℝ)) ^ 2)⁻¹) N).2 h
  simpa [Nat.cast_add] using h2

/-- Effective tail bound for the inverse-square series: for `N ≥ 1`,
`∑_{i ≥ 0} 1/(i+N)^2 ≤ 2/N`. -/
