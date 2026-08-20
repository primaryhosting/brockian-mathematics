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

lemma integral_d1A2 {A2 d1A2 : ℝ → ℝ → ℝ}
    (hd1 : ∀ x y : ℝ, HasDerivAt (fun t : ℝ => A2 t y) (d1A2 x y) x)
    (hc1 : Continuous fun p : ℝ × ℝ => d1A2 p.1 p.2) (y : ℝ) :
    (∫ x in (0:ℝ)..1, d1A2 x y) = A2 1 y - A2 0 y := by
  have hcont : Continuous fun x : ℝ => d1A2 x y :=
    hc1.comp (continuous_id.prodMk continuous_const)
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd1 x y)
    (hcont.intervalIntegrable 0 1)

/-- Integrating `∂₂A₁` over the Brillouin zone: it vanishes when `A₁` is periodic in `k₂`. -/
