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

theorem one_div_sq_le_telescope (x : ℝ) (hx : 2 ≤ x) : 1 / x ^ 2 ≤ 1 / (x - 1) - 1 / x := by
  have h1 : (0:ℝ) < x - 1 := by linarith
  have h2 : (0:ℝ) < x := by linarith
  have key : 1 / (x - 1) - 1 / x - 1 / x ^ 2 = 1 / ((x - 1) * x ^ 2) := by field_simp; ring
  have h3 : (0:ℝ) ≤ 1 / ((x - 1) * x ^ 2) := by positivity
  linarith

/-- Telescoping bound: `∑_{N < n ≤ M} 1/(n-1)^2 ≤ 1/(N-1) - 1/(M-1)`. -/
