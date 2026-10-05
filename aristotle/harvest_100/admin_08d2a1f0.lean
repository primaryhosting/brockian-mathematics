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
The family `p ↦ 1 / p`, indexed by the prime numbers, is not summable. -/
theorem reciprocal_sum_diverges : ¬ Summable (fun p : Nat.Primes ↦ (1 / p : ℝ)) :=
  Nat.Primes.not_summable_one_div

/-- A version of the divergence phrased over `ℕ`: the function on `ℕ` which is `1 / n` at
primes and `0` elsewhere is not summable. -/
theorem reciprocal_sum_diverges_indicator :
    ¬ Summable (Set.indicator {p : ℕ | p.Prime} (fun n : ℕ ↦ (1 : ℝ) / n)) :=
  not_summable_one_div_on_primes

/-- The partial sums of the reciprocals of the primes tend to infinity:
`∑_{p < n, p prime} 1 / p → ∞` as `n → ∞`. -/
theorem tendsto_sum_primesBelow_one_div_atTop :
    Filter.Tendsto (fun n : ℕ ↦ ∑ p ∈ Nat.primesBelow n, (1 : ℝ) / p)
      Filter.atTop Filter.atTop := by
  have hnonneg : ∀ n : ℕ, 0 ≤ Set.indicator {p : ℕ | p.Prime} (fun n : ℕ ↦ (1 : ℝ) / n) n :=
    fun n ↦ Set.indicator_nonneg (fun m _ ↦ by positivity) n
  have h := (not_summable_iff_tendsto_nat_atTop_of_nonneg hnonneg).mp
    reciprocal_sum_diverges_indicator
  refine h.congr (fun n ↦ ?_)
  rw [Finset.sum_indicator_eq_sum_filter]
  refine Finset.sum_congr ?_ (fun _ _ ↦ rfl)
  ext p
  simp [Nat.mem_primesBelow, Finset.mem_filter, Finset.mem_range]

end Primes

