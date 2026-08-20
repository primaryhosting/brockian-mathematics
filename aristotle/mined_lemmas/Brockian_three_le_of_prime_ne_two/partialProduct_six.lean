/-
# Singular Series Convergence Rate
Category: Brockian Corpus
Target: Brockian.SingularSeriesConvergenceRate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Singular Series Convergence Rate
Category: Brockian Corpus
Target: Brockian.SingularSeriesConvergenceRate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The singular series considered here is the Hardy–Littlewood twin-prime singular series
(without the leading factor `2`),
`𝔖 = ∏_{p odd prime} (1 - 1/(p-1)^2)`,
realised as the limit of its truncations `𝔖(N) = ∏_{p < N, p odd prime} (1 - 1/(p-1)^2)`.

The main result `Brockian.SingularSeriesConvergenceRate` is an *effective* convergence rate:
for every `N ≥ 3`,
`|𝔖(N) - 𝔖| ≤ 1/(N-2)`.
-/

namespace Brockian

open Finset

/-- The local factor at `p`: `1 - 1/(p-1)^2` at odd primes, and `1` at all other naturals. -/

lemma partialProduct_six : partialProduct 6 = 45 / 64 := by
  have h0 : ¬ Nat.Prime 0 := by decide
  have h1 : ¬ Nat.Prime 1 := by decide
  have h3 : Nat.Prime 3 := by norm_num
  have h4 : ¬ Nat.Prime 4 := by decide
  have h5 : Nat.Prime 5 := by norm_num
  simp [partialProduct, Finset.prod_range_succ, localFactor, h0, h1, h3, h4, h5]
  norm_num

/-- The singular series is positive: the infinite product does not degenerate to `0`. -/
