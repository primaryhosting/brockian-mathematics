import Mathlib

/-!
# Tknn Chern Hall
Category: Frontier Physics
Target: Frontier.tknn_chern_hall
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


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

/-- The Berry curvature `F = ∂₁A₂ - ∂₂A₁` of a `U(1)` Berry connection `A = (A₁, A₂)`
on the Brillouin zone. -/

theorem integral_berryCurvature_eq_boundary (L : ℝ) (hL : 0 ≤ L)
    (hA₂ : Continuous fun p : ℝ × ℝ => A₂ p.1 p.2)
    (hD₁ : Continuous fun p : ℝ × ℝ => D₁ p.1 p.2)
    (hD₂ : Continuous fun p : ℝ × ℝ => D₂ p.1 p.2)
    (hdx : ∀ x y : ℝ, HasDerivAt (fun t => A₂ t y) (D₂ x y) x)
    (hdy : ∀ x y : ℝ, HasDerivAt (fun t => A₁ x t) (D₁ x y) y) :
    (∫ y in (0:ℝ)..L, ∫ x in (0:ℝ)..L, berryCurvature A₁ A₂ x y)
      = (∫ y in (0:ℝ)..L, (A₂ L y - A₂ 0 y)) - ∫ x in (0:ℝ)..L, (A₁ x L - A₁ x 0) := by
  have hD₂cont : ∀ y : ℝ, Continuous fun x : ℝ => D₂ x y := fun y =>
    hD₂.comp (continuous_id.prodMk continuous_const)
  have hD₁cont : ∀ y : ℝ, Continuous fun x : ℝ => D₁ x y := fun y =>
    hD₁.comp (continuous_id.prodMk continuous_const)
  have hD₁cont' : ∀ x : ℝ, Continuous fun y : ℝ => D₁ x y := fun x =>
    hD₁.comp (continuous_const.prodMk continuous_id)
  -- inner integral in `x`
  have hinner : ∀ y : ℝ, (∫ x in (0:ℝ)..L, berryCurvature A₁ A₂ x y)
      = (A₂ L y - A₂ 0 y) - ∫ x in (0:ℝ)..L, D₁ x y := by
    intro y
    have hcongr : (∫ x in (0:ℝ)..L, berryCurvature A₁ A₂ x y)
        = ∫ x in (0:ℝ)..L, (D₂ x y - D₁ x y) := by
      refine intervalIntegral.integral_congr ?_
      intro x _
      exact berryCurvature_eq A₁ A₂ D₁ D₂ hdx hdy x y
    rw [hcongr, intervalIntegral.integral_sub
      ((hD₂cont y).intervalIntegrable _ _) ((hD₁cont y).intervalIntegrable _ _)]
    congr 1
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hdx x y)
      ((hD₂cont y).intervalIntegrable _ _)
  rw [intervalIntegral.integral_congr (g := fun y => (A₂ L y - A₂ 0 y) - ∫ x in (0:ℝ)..L, D₁ x y)
    (fun y _ => hinner y)]
  have hbdry : Continuous fun y : ℝ => A₂ L y - A₂ 0 y := by
    exact (hA₂.comp (continuous_const.prodMk continuous_id)).sub
      (hA₂.comp (continuous_const.prodMk continuous_id))
  have hparam : Continuous fun y : ℝ => ∫ x in (0:ℝ)..L, D₁ x y := by
    have hc : Continuous (Function.uncurry fun y x : ℝ => D₁ x y) :=
      hD₁.comp (continuous_snd.prodMk continuous_fst)
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hc
      continuous_const
  rw [intervalIntegral.integral_sub (hbdry.intervalIntegrable _ _)
    (hparam.intervalIntegrable _ _)]
  congr 1
  rw [interval_integral_swap D₁ L hL hD₁]
  refine intervalIntegral.integral_congr ?_
  intro x _
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hdy x y)
    ((hD₁cont' x).intervalIntegrable _ _))

end Stokes

/-- **TKNN.** For a Berry connection on the Brillouin torus `[0, L] × [0, L]` whose gauge is
periodic in the second momentum direction and whose transition function in the first direction
has winding number `n` (i.e. `A₂(L, ·) - A₂(0, ·) = 2πn/L`), the Chern number equals `n`. -/
