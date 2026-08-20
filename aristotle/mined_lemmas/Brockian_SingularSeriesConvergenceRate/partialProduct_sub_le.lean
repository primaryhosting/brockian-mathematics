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

lemma partialProduct_sub_le {N M : ℕ} (hN : 2 ≤ N) (hNM : N ≤ M) :
    partialProduct N - 1 / ((N : ℝ) - 1) ≤ partialProduct M := by
  have hprod : 1 - ∑ p ∈ Finset.Ico (N + 1) (M + 1), sTerm p
      ≤ ∏ p ∈ Finset.Ico (N + 1) (M + 1), (1 - sTerm p) :=
    one_sub_sum_le_prod_one_sub _ _ (fun i _ => sTerm_nonneg i) (fun i _ => sTerm_le_one i)
  have htail : ∑ p ∈ Finset.Ico (N + 1) (M + 1), sTerm p ≤ 1 / ((N : ℝ) - 1) :=
    tail_sum_le_bound N (M + 1) hN
  have hPN : 0 ≤ partialProduct N := partialProduct_nonneg N
  have hPN1 : partialProduct N ≤ 1 := partialProduct_le_one N
  have hT : 0 ≤ ∑ p ∈ Finset.Ico (N + 1) (M + 1), sTerm p :=
    Finset.sum_nonneg (fun i _ => sTerm_nonneg i)
  rw [partialProduct_split hNM]
  nlinarith

