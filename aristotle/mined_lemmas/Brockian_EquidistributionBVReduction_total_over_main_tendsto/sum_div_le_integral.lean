import Mathlib

/-!
# Total Over Main Tendsto
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.total_over_main_tendsto
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

set_option grind.warning false

namespace Brockian
namespace EquidistributionBVReduction

open Filter Finset

/-- The `N`-th equidistributed sample sum of `f`: the total of the values of `f` at the
`N` equidistributed sample points `0/N, 1/N, …, (N-1)/N` of the unit interval. -/

lemma sum_div_le_integral (hp : MonotoneOn p (Set.Icc (0:ℝ) 1)) {N : ℕ} (hN : 0 < N) :
    total p N / N ≤ ∫ x in (0:ℝ)..1, p x := by
  rw [← sum_piece_integrals hp hN, total, Finset.sum_div]
  exact Finset.sum_le_sum fun k hk => piece_lower hp (Finset.mem_range.1 hk)

/-- Quantitative error bound for left Riemann sums of a monotone function. -/
