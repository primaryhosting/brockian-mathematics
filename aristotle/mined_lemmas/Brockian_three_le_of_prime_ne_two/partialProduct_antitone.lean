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

lemma partialProduct_antitone : Antitone partialProduct := by
  intro M N hMN
  unfold partialProduct
  rw [← Finset.prod_range_mul_prod_Ico localFactor hMN]
  nlinarith [Finset.prod_nonneg (fun i (_ : i ∈ Finset.range M) => localFactor_nonneg i),
    Finset.prod_le_one (s := Finset.Ico M N) (fun i _ => localFactor_nonneg i)
      (fun i _ => localFactor_le_one i),
    Finset.prod_nonneg (fun i (_ : i ∈ Finset.Ico M N) => localFactor_nonneg i)]

