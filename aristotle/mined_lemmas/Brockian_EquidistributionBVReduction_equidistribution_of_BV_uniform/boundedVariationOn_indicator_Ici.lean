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
# Reduction of equidistribution to bounded–variation test functions

Let `x : ℕ → ℝ` be a sequence.  We say that the *bounded variation averages of `x`
converge* if for every real function `f` of bounded variation on `[0,1]` the Birkhoff-type
averages of `f` along the fractional parts of `x` converge to `∫_0^1 f`.

The main result, `Brockian.EquidistributionBVReduction.equidistribution_of_BV_uniform`,
says that this hypothesis on `x` forces `x` to be uniformly distributed mod `1`:
the proportion of the first `N` fractional parts falling into a subinterval `[a,b) ⊆ [0,1]`
tends to its length `b - a`.

The point of the reduction is that indicator functions of intervals are of bounded
variation; this is proved here from scratch (`Brockian.EquidistributionBVReduction.boundedVariationOn_indicator_Ico`),
via a subadditivity estimate for `eVariationOn` and the fact that the two half-line
indicators `1_{[a,∞)}` and `1_{[b,∞)}` are monotone.
-/

open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace Brockian
namespace EquidistributionBVReduction

/-- A sequence `x : ℕ → ℝ` is *uniformly distributed mod 1* if for every subinterval
`[a,b) ⊆ [0,1]`, the proportion of `n < N` with `Int.fract (x n) ∈ [a, b)` tends to `b - a`. -/

theorem boundedVariationOn_indicator_Ici (c : ℝ) :
    BoundedVariationOn (fun t : ℝ => if c ≤ t then (1 : ℝ) else 0) (Set.Icc (0 : ℝ) 1) := by
  have hmono : Monotone fun t : ℝ => if c ≤ t then (1 : ℝ) else 0 := by
    intro s t hst
    by_cases hs : c ≤ s
    · simp [hs, hs.trans hst]
    · simp only [hs, if_false]
      split <;> norm_num
  have h := (hmono.monotoneOn (Set.Icc (0 : ℝ) 1)).eVariationOn_le
    (a := (0 : ℝ)) (b := (1 : ℝ)) (by norm_num) (by norm_num)
  rw [Set.inter_self] at h
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top h

/-- The indicator function of an interval `[a, b)` has bounded variation on `[0,1]`. -/
