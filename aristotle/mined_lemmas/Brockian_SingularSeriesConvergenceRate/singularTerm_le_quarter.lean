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

lemma singularTerm_le_quarter (n : ℕ) : singularTerm n ≤ 1 / 4 := by
  unfold singularTerm
  split
  · rename_i h
    have h3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h.2
    rw [div_le_div_iff₀ (by nlinarith) (by norm_num)]
    nlinarith
  · norm_num

