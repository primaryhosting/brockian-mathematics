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

lemma tail_sum_le (N : ℕ) (hN : 2 ≤ N) :
    ∀ M : ℕ, N + 1 ≤ M →
      ∑ p ∈ Finset.Ico (N + 1) M, sTerm p ≤ 1 / ((N : ℝ) - 1) - 1 / ((M : ℝ) - 2) := by
  intro M hM
  induction M, hM using Nat.le_induction with
  | base =>
      have : ((N : ℝ) + 1) - 2 = (N : ℝ) - 1 := by ring
      simp [this]
  | succ M hM ih =>
      rw [Finset.sum_Ico_succ_top (by omega)]
      have h3 : 3 ≤ M := by omega
      have hstep := sTerm_le_telescope h3
      have hcast : ((M : ℝ) + 1) - 2 = (M : ℝ) - 1 := by ring
      push_cast
      rw [hcast]
      have := ih
      linarith

/-- The tail of the sum of local exponents beyond `N` is at most `1/(N-1)`. -/
