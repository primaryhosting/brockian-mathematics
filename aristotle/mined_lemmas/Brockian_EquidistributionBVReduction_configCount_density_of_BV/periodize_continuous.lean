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
# Equidistribution: reduction from continuous test functions to BV (indicator) test functions

This file contains the classical "bounded variation reduction" step in the theory of
equidistribution modulo one: if a sequence `x : ℕ → ℝ` is equidistributed mod `1` in Weyl's
sense (Cesàro averages of *continuous* `1`-periodic test functions converge to the mean of the
test function), then the counting density of the "configurations" `n ↦ Int.fract (x n)` lying in
a subinterval `[a, b) ⊆ [0, 1)` converges to the length `b - a`.

The indicator of an interval is the basic example of a function of bounded variation which is not
continuous, so the content of the main theorem is exactly that the class of admissible test
functions may be enlarged from continuous functions to such BV functions.

The main result is `Brockian.EquidistributionBVReduction.configCount_density_of_BV`; it is
unconditional apart from the (necessary) equidistribution hypothesis on the sequence itself.
-/

open Filter Set MeasureTheory
open scoped Topology BigOperators Classical

namespace Brockian.EquidistributionBVReduction

/-- The number of indices `n < N` whose fractional part `Int.fract (x n)` lies in `[a, b)`. -/

lemma periodize_continuous {f : ℝ → ℝ} (hf : f 0 = f 1) (hc : ContinuousOn f (Set.Icc 0 1)) :
    Continuous (periodize f) := by
  haveI : Fact ((0:ℝ) < 1) := ⟨one_pos⟩
  have key : periodize f = (AddCircle.liftIco 1 0 f) ∘ ((↑) : ℝ → AddCircle (1:ℝ)) := by
    funext t
    have ht : Int.fract t ∈ Set.Ico (0:ℝ) 1 := ⟨Int.fract_nonneg t, Int.fract_lt_one t⟩
    have hcoe : ((Int.fract t : ℝ) : AddCircle (1:ℝ)) = (t : AddCircle (1:ℝ)) := by
      have h0 : ((Int.fract t : ℝ) : AddCircle (1:ℝ)) - (t : AddCircle (1:ℝ)) = 0 := by
        rw [← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff]
        exact ⟨-⌊t⌋, by rw [Int.fract]; ring⟩
      exact sub_eq_zero.mp h0
    simp only [Function.comp_apply, ← hcoe, periodize]
    exact (AddCircle.liftIco_zero_coe_apply ht).symm
  rw [key]
  exact (AddCircle.liftIco_zero_continuous hf hc).comp continuous_coinduced_rng

/-- The continuous trapezoidal test function: it vanishes outside `(a, b)`, equals `1` on
`[a + d, b - d]` and interpolates linearly in between. -/
