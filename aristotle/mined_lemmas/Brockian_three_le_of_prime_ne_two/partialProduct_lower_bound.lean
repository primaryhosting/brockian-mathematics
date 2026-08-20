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

lemma partialProduct_lower_bound {N M : ℕ} (hN : 3 ≤ N) (hNM : N ≤ M) :
    partialProduct N * (1 - 1 / ((N : ℝ) - 2)) ≤ partialProduct M := by
  have hN' : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hsplit : partialProduct M
      = partialProduct N * ∏ p ∈ Finset.Ico N M, localFactor p := by
    unfold partialProduct
    rw [Finset.prod_range_mul_prod_Ico localFactor hNM]
  have hweier : 1 - ∑ p ∈ Finset.Ico N M, (1 - localFactor p)
      ≤ ∏ p ∈ Finset.Ico N M, (1 - (1 - localFactor p)) := by
    refine one_sub_sum_le_prod_one_sub (fun i _ => one_sub_localFactor_nonneg i) ?_
    intro i _
    have := localFactor_nonneg i
    linarith
  have hsimp : ∏ p ∈ Finset.Ico N M, (1 - (1 - localFactor p))
      = ∏ p ∈ Finset.Ico N M, localFactor p := by
    apply Finset.prod_congr rfl
    intro i _
    ring
  rw [hsimp] at hweier
  have htail := sum_one_sub_localFactor_le hN hNM
  have hMpos : (0 : ℝ) ≤ 1 / ((M : ℝ) - 2) := by
    have hM : (3 : ℝ) ≤ (M : ℝ) := by
      have : 3 ≤ M := le_trans hN hNM
      exact_mod_cast this
    exact div_nonneg zero_le_one (by linarith)
  have hlow : 1 - 1 / ((N : ℝ) - 2) ≤ ∏ p ∈ Finset.Ico N M, localFactor p := by
    linarith
  rw [hsplit]
  exact mul_le_mul_of_nonneg_left hlow (partialProduct_nonneg N)

