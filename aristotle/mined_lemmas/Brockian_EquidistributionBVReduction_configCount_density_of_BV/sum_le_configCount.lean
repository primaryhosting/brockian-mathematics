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

import Mathlib

/-!
# Equidistribution and the bounded-variation reduction for configuration counts

Let `u : ℕ → ℝ` be a sequence which is *equidistributed* in the unit interval, in the sense
that averages of continuous test functions along `u` converge to the corresponding integral
over `[0,1]` (`Brockian.EquidistributionBVReduction.Equidistributed`).

The main result, `Brockian.EquidistributionBVReduction.configCount_density_of_BV`, upgrades
this from continuous test functions to the indicator of an interval `[a, b) ⊆ [0,1]`, which is
the basic function of bounded variation: the number of indices `n < N` with `u n ∈ [a, b)`
has density `b - a`.

The proof is the usual sandwich argument: the indicator of `[a, b)` is squeezed between two
continuous functions (produced by Urysohn's lemma) whose integrals differ from `b - a` by an
arbitrarily small amount.
-/

open MeasureTheory Set Filter Topology

namespace Brockian
namespace EquidistributionBVReduction

open Classical in
/-- `configCount u S N` is the number of indices `n < N` for which `u n` lies in `S`. -/

lemma sum_le_configCount (u : ℕ → ℝ) (S : Set ℝ) (N : ℕ) (g : ℝ → ℝ)
    (h1 : ∀ x, g x ≤ 1) (hsupp : ∀ x ∉ S, g x = 0) :
    ∑ n ∈ Finset.range N, g (u n) ≤ (configCount u S N : ℝ) := by
  rw [configCount_eq_sum_indicator]
  refine Finset.sum_le_sum fun n _ => ?_
  by_cases hn : u n ∈ S
  · simpa [Set.indicator_of_mem hn] using h1 (u n)
  · simp [Set.indicator_of_notMem hn, hsupp _ hn]

/-- A nonnegative continuous function bounded by `1` and supported in `(p, q)` has integral over
`[0,1]` at most `q - p`. -/
