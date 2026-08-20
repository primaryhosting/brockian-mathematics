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

lemma three_quarters_le_localFactor (p : ℕ) : (3 : ℝ) / 4 ≤ localFactor p := by
  unfold localFactor
  split
  · rename_i h
    have hp3 : 3 ≤ p := three_le_of_prime_ne_two h.1 h.2
    have hp3' : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
    have hx : (4 : ℝ) ≤ ((p : ℝ) - 1) ^ 2 := by nlinarith
    have h4 : (0 : ℝ) < 4 := by norm_num
    have : 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 / 4 := by
      apply one_div_le_one_div_of_le h4 hx
    linarith
  · norm_num

