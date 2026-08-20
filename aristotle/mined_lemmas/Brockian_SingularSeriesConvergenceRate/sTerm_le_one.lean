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

lemma sTerm_le_one (p : ℕ) : sTerm p ≤ 1 := by
  unfold sTerm
  split
  · rename_i h
    have h3 : 3 ≤ p := three_le_of_prime_ne_two h.1 h.2
    have hx : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h3
    rw [div_le_one (by nlinarith)]
    nlinarith
  · norm_num

/-- The key telescoping estimate: `1/(p-1)^2 ≤ 1/(p-2) - 1/(p-1)` for `p ≥ 3`. -/
