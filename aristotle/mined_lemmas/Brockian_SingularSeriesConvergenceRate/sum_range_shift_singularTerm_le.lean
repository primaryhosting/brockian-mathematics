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

lemma sum_range_shift_singularTerm_le {N : ℕ} (hN : 3 ≤ N) (m : ℕ) :
    ∑ i ∈ Finset.range m, singularTerm (i + N)
      ≤ 1 / ((N : ℝ) - 2) - 1 / ((m : ℝ) + (N : ℝ) - 2) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ]
      have hk : 3 ≤ m + N := by omega
      have h := singularTerm_le_telescope hk
      have hcast : ((m + N : ℕ) : ℝ) = (m : ℝ) + (N : ℝ) := by push_cast; ring
      rw [hcast] at h
      have hcast2 : ((m : ℝ) + 1) + (N : ℝ) - 2 = (m : ℝ) + (N : ℝ) - 1 := by ring
      push_cast
      rw [hcast2]
      linarith

/-- The tail of the singular series over an interval is at most `1/(N-2)`. -/
