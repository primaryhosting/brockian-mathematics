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

theorem singularSeries_pos : 0 < singularSeries := by
  have h := le_singularSeries (N := 6) (by norm_num)
  rw [partialProduct_six] at h
  norm_num at h
  linarith

/-! ### The main theorem -/

/-- **Effective convergence rate for the singular series.**
For every `N ≥ 3`, the truncated Hardy–Littlewood twin-prime singular series
`𝔖(N) = ∏_{p < N, p odd prime} (1 - 1/(p-1)^2)` approximates its limit `𝔖` with error at most
`1/(N-2)`. -/
