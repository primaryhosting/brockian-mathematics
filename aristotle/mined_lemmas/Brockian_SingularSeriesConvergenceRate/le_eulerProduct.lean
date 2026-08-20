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

namespace Brockian

/-! ## The twin-prime singular series and an effective rate of convergence

We study the Hardy–Littlewood singular series for prime pairs,
`𝔖 = 2 * ∏_{p odd prime} (1 - 1/(p-1)^2)`,
realised as the limit of its truncations `𝔖(N) = 2 * ∏_{p ≤ N, p odd prime} (1 - 1/(p-1)^2)`.

The main result `Brockian.SingularSeriesConvergenceRate` is an *effective* bound on the
error committed by truncating at `N`:  `|𝔖(N) - 𝔖| ≤ 2 / (N - 1)`. -/

/-- The local factor exponent: `sTerm p = 1/(p-1)^2` for an odd prime `p`, and `0` otherwise. -/

lemma le_eulerProduct {N : ℕ} (hN : 2 ≤ N) :
    partialProduct N - 1 / ((N : ℝ) - 1) ≤ eulerProduct := by
  refine le_ciInf ?_
  intro M
  rcases le_total N M with h | h
  · exact partialProduct_sub_le hN h
  · have h1 : partialProduct N ≤ partialProduct M := partialProduct_antitone h
    have h2 : (0 : ℝ) < (N : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      linarith
    have : 0 < 1 / ((N : ℝ) - 1) := by positivity
    linarith

/-- The truncated singular series converges to the singular series. -/
