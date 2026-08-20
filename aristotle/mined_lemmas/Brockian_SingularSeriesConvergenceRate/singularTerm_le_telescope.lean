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

lemma singularTerm_le_telescope {k : ℕ} (hk : 3 ≤ k) :
    singularTerm k ≤ 1 / ((k : ℝ) - 2) - 1 / ((k : ℝ) - 1) := by
  have h3 : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk2 : (0 : ℝ) < (k : ℝ) - 2 := by linarith
  have hk1 : (0 : ℝ) < (k : ℝ) - 1 := by linarith
  have key : 1 / ((k : ℝ) - 2) - 1 / ((k : ℝ) - 1) = 1 / (((k : ℝ) - 2) * ((k : ℝ) - 1)) := by
    field_simp
    ring
  rw [key]
  unfold singularTerm
  split
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  · positivity

/-- Effective bound on partial sums of the tail of the singular series. -/
