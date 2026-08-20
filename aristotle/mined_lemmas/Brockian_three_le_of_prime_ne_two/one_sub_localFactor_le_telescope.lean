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

lemma one_sub_localFactor_le_telescope {p : ℕ} (hp : 3 ≤ p) :
    1 - localFactor p ≤ 1 / ((p : ℝ) - 2) - 1 / ((p : ℝ) - 1) := by
  have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have h1 : (0 : ℝ) < (p : ℝ) - 2 := by linarith
  have h2 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have key : 1 / ((p : ℝ) - 2) - 1 / ((p : ℝ) - 1) = 1 / (((p : ℝ) - 2) * ((p : ℝ) - 1)) := by
    field_simp
    ring
  rw [key]
  unfold localFactor
  split
  · have : 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 / (((p : ℝ) - 2) * ((p : ℝ) - 1)) := by
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith
    linarith
  · have : (0 : ℝ) < 1 / (((p : ℝ) - 2) * ((p : ℝ) - 1)) := by positivity
    linarith

/-! ### A Weierstrass-type product inequality -/

