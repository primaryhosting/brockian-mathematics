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

lemma le_singularSeries {N : ℕ} (hN : 3 ≤ N) :
    partialProduct N * (1 - 1 / ((N : ℝ) - 2)) ≤ singularSeries := by
  apply le_ciInf
  intro M
  rcases le_total N M with h | h
  · exact partialProduct_lower_bound hN h
  · have h1 : partialProduct N ≤ partialProduct M := partialProduct_antitone h
    have hN' : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have h2 : (0 : ℝ) ≤ 1 / ((N : ℝ) - 2) := div_nonneg zero_le_one (by linarith)
    nlinarith [partialProduct_nonneg N]

/-- The truncation at `6` only sees the primes `3` and `5`. -/
