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

lemma sum_one_sub_localFactor_le {N M : ℕ} (hN : 3 ≤ N) (hNM : N ≤ M) :
    ∑ p ∈ Finset.Ico N M, (1 - localFactor p) ≤ 1 / ((N : ℝ) - 2) - 1 / ((M : ℝ) - 2) := by
  induction M, hNM using Nat.le_induction with
  | base => simp
  | succ M hNM ih =>
      have hM3 : 3 ≤ M := le_trans hN hNM
      have hM : (3 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM3
      rw [Finset.sum_Ico_succ_top hNM]
      have hstep := one_sub_localFactor_le_telescope hM3
      have hcast : ((M + 1 : ℕ) : ℝ) - 2 = (M : ℝ) - 1 := by push_cast; ring
      rw [hcast]
      linarith

