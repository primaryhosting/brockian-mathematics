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

theorem boundedVariationOn_indicator_Ico {a b : ℝ} (hab : a ≤ b) :
    BoundedVariationOn (Set.indicator (Set.Ico a b) (fun _ => (1 : ℝ))) (Set.Icc (0 : ℝ) 1) := by
  have heq : Set.EqOn (Set.indicator (Set.Ico a b) (fun _ => (1 : ℝ)))
      (fun t : ℝ => (if a ≤ t then (1 : ℝ) else 0) - (if b ≤ t then (1 : ℝ) else 0))
      (Set.Icc (0 : ℝ) 1) := by
    intro t _
    by_cases hb : b ≤ t
    · have ha : a ≤ t := hab.trans hb
      simp [ha, hb]
    · push_neg at hb
      by_cases ha : a ≤ t
      · have : t ∈ Set.Ico a b := ⟨ha, hb⟩
        simp [Set.indicator_of_mem this, ha, not_le.2 hb]
      · push_neg at ha
        simp [not_le.2 ha, not_le.2 hb]
  unfold BoundedVariationOn
  rw [eVariationOn.eq_of_eqOn heq]
  refine ne_top_of_le_ne_top ?_ (eVariationOn_sub_le _ _ _)
  exact ENNReal.add_ne_top.2 ⟨boundedVariationOn_indicator_Ici a, boundedVariationOn_indicator_Ici b⟩

/-! ### The integral of an interval indicator -/

/-- The integral over `[0,1]` of the indicator of `[a,b) ⊆ [0,1]` is `b - a`. -/
