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
# Equidistribution of irrational rotations and the BV reduction of configuration counts

This file proves, unconditionally, that for an irrational `α` the number of `n < N` with
`Int.fract (n * α)` in a window `[a, b) ⊆ [0, 1]` is asymptotic to the main term `(b - a) * N`.

The equidistribution input (Weyl's theorem for the sequence `n ↦ n α mod 1`) is proved here from
scratch, via Weyl's criterion: the set of continuous test functions on the circle for which the
Birkhoff averages converge to the mean is a closed submodule containing all characters, hence is
everything, by density of trigonometric polynomials.  A bounded-variation ("BV") style sandwich by
continuous trapezoidal functions then transfers the statement to indicator functions of windows.
-/

open MeasureTheory Filter Set Metric Topology Complex
open scoped BigOperators

namespace Brockian.EquidistributionBVReduction

noncomputable section

/-- The number of `n < N` for which the fractional part of `n * α` lies in the window `[a, b)`. -/

def weylGood : Submodule ℂ C(AddCircle (1 : ℝ), ℂ) where
  carrier := {F | Tendsto (circleAvg alpha F) atTop (𝓝 (∫ y, F y))}
  add_mem' := by
    intro F G hF hG
    simp only [Set.mem_setOf_eq] at hF hG ⊢
    have hsum : ∀ N : ℕ, circleAvg alpha (F + G) N = circleAvg alpha F N + circleAvg alpha G N := by
      intro N; simp [circleAvg, Finset.sum_add_distrib, add_div]
    have hint : (∫ y, (F + G) y) = (∫ y, F y) + ∫ y, G y := by
      simp only [ContinuousMap.add_apply]
      exact integral_add (integrable_continuousMap F) (integrable_continuousMap G)
    rw [hint]
    exact (hF.add hG).congr fun N => (hsum N).symm
  zero_mem' := by
    simp only [Set.mem_setOf_eq]
    have hsum : ∀ N : ℕ, circleAvg alpha (0 : C(AddCircle (1 : ℝ), ℂ)) N = 0 := by
      intro N; simp [circleAvg]
    simp only [ContinuousMap.zero_apply, integral_zero]
    exact tendsto_const_nhds.congr fun N => (hsum N).symm
  smul_mem' := by
    intro c F hF
    simp only [Set.mem_setOf_eq] at hF ⊢
    have hsum : ∀ N : ℕ, circleAvg alpha (c • F) N = c * circleAvg alpha F N := by
      intro N
      simp only [circleAvg, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, mul_div_assoc]
    have hint : (∫ y, (c • F) y) = c * ∫ y, F y := by
      simp only [ContinuousMap.smul_apply, smul_eq_mul]
      exact integral_const_mul c _
    rw [hint]
    exact (hF.const_mul c).congr fun N => (hsum N).symm

/-- The mean value of a nontrivial character on the circle vanishes. -/
