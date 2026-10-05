import Mathlib

/-!
# Reciprocal Sum Diverges
Category: Frontier — Prime Numbers
Target: Primes.reciprocal_sum_diverges
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Primes

/-- **Euler's theorem on the divergence of the sum of prime reciprocals.**
The family `p ↦ 1 / p`, indexed by the primes, is not summable. -/
theorem reciprocal_sum_diverges : ¬ Summable (fun p : Nat.Primes ↦ (1 / p : ℝ)) :=
  Nat.Primes.not_summable_one_div

/-- Equivalent formulation of the divergence, as a statement about the function
`n ↦ 1 / n` on `ℕ` restricted (via the indicator) to the set of primes. -/
theorem reciprocal_sum_diverges_indicator :
    ¬ Summable (Set.indicator {p : ℕ | p.Prime} (fun n : ℕ ↦ (1 : ℝ) / n)) :=
  not_summable_one_div_on_primes

/-- The partial sums `∑_{p < n, p prime} 1/p` tend to infinity. -/
theorem tendsto_sum_one_div_primesBelow_atTop :
    Filter.Tendsto (fun n : ℕ ↦ ∑ p ∈ Nat.primesBelow n, (1 : ℝ) / p)
      Filter.atTop Filter.atTop := by
  have hnonneg : ∀ n : ℕ, 0 ≤ Set.indicator {p : ℕ | p.Prime} (fun n : ℕ ↦ (1 : ℝ) / n) n :=
    fun n ↦ Set.indicator_nonneg (fun p _ ↦ by positivity) n
  have key := (not_summable_iff_tendsto_nat_atTop_of_nonneg hnonneg).mp
    reciprocal_sum_diverges_indicator
  refine key.congr (fun n ↦ ?_)
  rw [Finset.sum_indicator_eq_sum_filter]
  congr 1

end Primes

