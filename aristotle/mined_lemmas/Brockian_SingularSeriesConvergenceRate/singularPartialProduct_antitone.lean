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

lemma singularPartialProduct_antitone {N M : ℕ} (h : N ≤ M) :
    singularPartialProduct M ≤ singularPartialProduct N := by
  rw [singularPartialProduct_split h]
  have hq0 : 0 ≤ ∏ p ∈ Finset.Ico N M, singularFactor p :=
    Finset.prod_nonneg (fun i _ => singularFactor_nonneg i)
  have hq1 : ∏ p ∈ Finset.Ico N M, singularFactor p ≤ 1 :=
    Finset.prod_le_one (fun i _ => singularFactor_nonneg i) (fun i _ => singularFactor_le_one i)
  nlinarith [singularPartialProduct_nonneg N, singularPartialProduct_le_one N]

/-- **Singular Series Convergence Rate.**
The truncated singular series products form a Cauchy sequence with the effective rate
`|S_N - S_M| ≤ 1/(N-2)` for all `3 ≤ N ≤ M`; in particular the truncation error of the
singular series at `N` is `O(1/N)`. -/
