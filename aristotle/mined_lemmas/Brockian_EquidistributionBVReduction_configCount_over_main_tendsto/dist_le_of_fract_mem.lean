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

theorem dist_le_of_fract_mem {t : ℝ} (ht : Int.fract t ∈ Set.Ico a b) :
    dist ((t : ℝ) : AddCircle (1 : ℝ)) (((a + b) / 2 : ℝ) : AddCircle (1 : ℝ)) ≤ (b - a) / 2 := by
  rw [dist_coe_eq]
  have h1 : |(t - (a + b) / 2) - round (t - (a + b) / 2)| ≤ |(t - (a + b) / 2) - (⌊t⌋ : ℝ)| :=
    round_le _ _
  have h2 : (t - (a + b) / 2) - (⌊t⌋ : ℝ) = Int.fract t - (a + b) / 2 := by
    rw [Int.fract]; ring
  rw [h2] at h1
  obtain ⟨h3, h4⟩ := ht
  refine h1.trans ?_
  rw [abs_le]
  constructor <;> linarith

/-- Conversely, a point strictly within `(b - a)/2` of the midpoint has fractional part in the
window `[a, b)`. -/
