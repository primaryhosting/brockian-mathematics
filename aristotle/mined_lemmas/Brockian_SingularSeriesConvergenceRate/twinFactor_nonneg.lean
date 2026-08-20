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

theorem twinFactor_nonneg {p : ℕ} (hp : 3 ≤ p) : 0 ≤ twinFactor p := by
  have h3 : (3:ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have h2 : (2:ℝ) ≤ (p : ℝ) - 1 := by linarith
  have : (1:ℝ) ≤ ((p : ℝ) - 1) ^ 2 := by nlinarith
  have hpos : (0:ℝ) < ((p : ℝ) - 1) ^ 2 := by nlinarith
  rw [twinFactor, sub_nonneg, div_le_one hpos]
  exact this

