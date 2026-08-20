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

lemma tail_sum_le_bound (N M : ℕ) (hN : 2 ≤ N) :
    ∑ p ∈ Finset.Ico (N + 1) M, sTerm p ≤ 1 / ((N : ℝ) - 1) := by
  rcases lt_or_ge M (N + 1) with h | h
  · rw [Finset.Ico_eq_empty (by omega)]
    have : (1 : ℝ) ≤ (N : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      linarith
    simp only [Finset.sum_empty]
    positivity
  · have h1 := tail_sum_le N hN M h
    have h2 : (0 : ℝ) < (M : ℝ) - 2 := by
      have : (3 : ℝ) ≤ (M : ℝ) := by exact_mod_cast (by omega : 3 ≤ M)
      linarith
    have : 0 < 1 / ((M : ℝ) - 2) := by positivity
    linarith

/-- Weierstrass-type inequality: `∏ (1 - a i) ≥ 1 - ∑ a i` for `0 ≤ a i ≤ 1`. -/
