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

namespace Frontier

open MeasureTheory intervalIntegral

/-- The Berry curvature `F₁₂ = ∂₁A₂ - ∂₂A₁` of a Berry connection `A = (A₁, A₂)` on the
Brillouin zone, given the two partial derivatives `d1A2 = ∂₁A₂` and `d2A1 = ∂₂A₁`. -/

lemma integral_square_swap {g : ℝ → ℝ → ℝ}
    (hg : Continuous fun p : ℝ × ℝ => g p.1 p.2) :
    (∫ y in (0:ℝ)..1, ∫ x in (0:ℝ)..1, g x y)
      = ∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1, g x y := by
  have h01 : (0:ℝ) ≤ 1 := zero_le_one
  simp_rw [intervalIntegral.integral_of_le h01]
  exact (MeasureTheory.integral_integral_swap
    (integrable_uncurry_of_continuous hg)).symm

/-- Integrating `∂₁A₂` over the Brillouin zone: only the winding of `A₂` in the `k₁`
direction survives. -/
