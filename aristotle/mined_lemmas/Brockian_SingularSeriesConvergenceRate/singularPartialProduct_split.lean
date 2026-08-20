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

lemma singularPartialProduct_split {N M : ℕ} (h : N ≤ M) :
    singularPartialProduct M
      = singularPartialProduct N * ∏ p ∈ Finset.Ico N M, singularFactor p := by
  unfold singularPartialProduct
  simp only [Finset.range_eq_Ico]
  rw [Finset.prod_Ico_consecutive _ (Nat.zero_le N) h]

