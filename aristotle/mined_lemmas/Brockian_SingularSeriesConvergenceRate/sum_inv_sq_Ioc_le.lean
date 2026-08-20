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

theorem sum_inv_sq_Ioc_le {N : ℕ} (hN : 2 ≤ N) :
    ∀ M : ℕ, N ≤ M →
      ∑ n ∈ Finset.Ioc N M, 1 / ((n : ℝ) - 1) ^ 2 ≤ 1 / ((N : ℝ) - 1) - 1 / ((M : ℝ) - 1) := by
  intro M hM
  induction M, hM using Nat.le_induction with
  | base => simp
  | succ M hM ih =>
      have hM2 : (2:ℝ) ≤ (M : ℝ) := by
        have : (2:ℕ) ≤ M := le_trans hN hM
        exact_mod_cast this
      rw [Finset.sum_Ioc_succ_top (by omega)]
      push_cast
      have haux := one_div_sq_le_telescope (M : ℝ) hM2
      have hs : ((M:ℝ) + 1 - 1) = (M:ℝ) := by ring
      rw [hs]
      linarith

/-- Effective Cauchy estimate for the partial products. -/
