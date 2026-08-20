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

lemma singularPartialProduct_le_one (N : ℕ) : singularPartialProduct N ≤ 1 :=
  Finset.prod_le_one (fun i _ => singularFactor_nonneg i) (fun i _ => singularFactor_le_one i)

