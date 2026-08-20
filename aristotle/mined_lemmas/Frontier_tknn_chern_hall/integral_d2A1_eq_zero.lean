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

lemma integral_d2A1_eq_zero {A1 d2A1 : ℝ → ℝ → ℝ}
    (hd2 : ∀ x y : ℝ, HasDerivAt (fun t : ℝ => A1 x t) (d2A1 x y) y)
    (hc2 : Continuous fun p : ℝ × ℝ => d2A1 p.1 p.2)
    (hper : ∀ x : ℝ, A1 x 1 = A1 x 0) :
    (∫ y in (0:ℝ)..1, ∫ x in (0:ℝ)..1, d2A1 x y) = 0 := by
  rw [integral_square_swap hc2]
  have : ∀ x : ℝ, (∫ y in (0:ℝ)..1, d2A1 x y) = 0 := by
    intro x
    have hcont : Continuous fun y : ℝ => d2A1 x y :=
      hc2.comp (continuous_const.prodMk continuous_id)
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t : ℝ => A1 x t)
      (f' := fun y : ℝ => d2A1 x y) (fun y _ => hd2 x y) (hcont.intervalIntegrable 0 1)
    rw [this]
    simp [hper x]
  simp [this]

/-- **TKNN (base case).** For a Berry connection `A = (A₁, A₂)` on the Brillouin zone torus
`[0,1]²` whose gauge is periodic in `k₂` and whose transition function in the `k₁` direction
has winding number `n` (i.e. `A₂(1, k₂) = A₂(0, k₂) + 2πn`), the Chern number of the Berry
curvature `F₁₂ = ∂₁A₂ - ∂₂A₁` is the integer `n`, and consequently the Hall conductance given
by the Kubo formula is quantized:  `σ_xy = n · e²/h`. -/
