import Mathlib

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

/-!
# An effective convergence rate for the twin-prime singular series

The Hardy–Littlewood singular series for prime pairs `(n, n + 2)` is

  `𝔖 = 2 * ∏_{p odd prime} (1 - 1/(p-1)^2)`,

the product being over all odd primes.  In this file we define the partial products
`Brockian.twinPartial N` (product over the odd primes `p ≤ N`), show they converge, and
prove an *effective* rate of convergence:

  `|Brockian.singularSeriesPartial N - Brockian.singularSeries| ≤ 2 / (N - 1)`  for `N ≥ 3`.
-/

namespace Brockian

open Filter Finset
open scoped Topology

/-- The set of odd primes `p ≤ N`, as a `Finset`. -/

theorem twinPartial_sub_twinPrimeConstant_le {N : ℕ} (hN : 3 ≤ N) :
    |twinPartial N - twinPrimeConstant| ≤ 1 / ((N : ℝ) - 1) := by
  have hle : twinPrimeConstant ≤ twinPartial N := twinPrimeConstant_le N
  have hupper : twinPartial N - twinPrimeConstant ≤ 1 / ((N : ℝ) - 1) := by
    have hlim : Tendsto (fun M => twinPartial N - twinPartial M) atTop
        (𝓝 (twinPartial N - twinPrimeConstant)) := by
      exact (tendsto_const_nhds).sub twinPartial_tendsto
    refine le_of_tendsto hlim ?_
    filter_upwards [eventually_ge_atTop N] with M hM
    exact twinPartial_sub_le hN hM
  rw [abs_of_nonneg (by linarith)]
  exact hupper

/-- **Effective convergence-rate bound for the singular series.**
For every `N ≥ 3`, the truncation `singularSeriesPartial N = 2 ∏_{3 ≤ p ≤ N} (1 - 1/(p-1)^2)`
of the Hardy–Littlewood singular series for prime pairs approximates `𝔖` with error at most
`2/(N-1)`. -/
