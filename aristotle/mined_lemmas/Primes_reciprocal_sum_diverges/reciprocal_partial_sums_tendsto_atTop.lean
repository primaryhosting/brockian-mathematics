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

namespace Primes

/-- **Euler**: the sum of the reciprocals of the primes diverges, i.e. the family
`p ↦ 1 / p` indexed by the primes is not summable. -/

theorem reciprocal_partial_sums_tendsto_atTop :
    Filter.Tendsto
      (fun N : ℕ ↦ ∑ p ∈ (Finset.range N).filter Nat.Prime, (1 : ℝ) / p)
      Filter.atTop Filter.atTop := by
  have hnonneg : ∀ n : ℕ,
      0 ≤ Set.indicator {p : ℕ | p.Prime} (fun n : ℕ ↦ (1 : ℝ) / n) n := by
    intro n
    exact Set.indicator_apply_nonneg fun _ ↦ by positivity
  have h := (not_summable_iff_tendsto_nat_atTop_of_nonneg hnonneg).mp
    reciprocal_sum_diverges_indicator
  refine h.congr fun N ↦ ?_
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  by_cases hn : n.Prime <;> simp [hn]

end Primes

