/-
# Singular Series Convergence Rate
Category: Brockian Corpus
Target: Brockian.SingularSeriesConvergenceRate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring `/-! ... -/`, so the header
-- above is written as an ordinary block comment and repeated as a module docstring below.)

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

/-- The `p`-th term of the (twin-prime) singular series: `1/(p-1)^2` for odd primes `p`,
and `0` otherwise. -/

lemma sum_Ico_singularTerm_le {N M : ℕ} (hN : 3 ≤ N) :
    ∑ p ∈ Finset.Ico N M, singularTerm p ≤ 1 / ((N : ℝ) - 2) := by
  rw [Finset.sum_Ico_eq_sum_range]
  have h := sum_range_shift_singularTerm_le hN (M - N)
  have hpos : (0 : ℝ) ≤ 1 / (((M - N : ℕ) : ℝ) + (N : ℝ) - 2) := by
    have h3 : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have h4 : (0 : ℝ) ≤ ((M - N : ℕ) : ℝ) := Nat.cast_nonneg _
    exact div_nonneg (by norm_num) (by linarith)
  have heq : ∀ k : ℕ, singularTerm (N + k) = singularTerm (k + N) := by
    intro k; rw [Nat.add_comm]
  simp only [heq]
  linarith

/-- **Effective convergence rate for the singular series (sum form).**
The tail `∑_{p ≥ N} 1/(p-1)^2` of the singular series is at most `1/(N-2)`. -/
