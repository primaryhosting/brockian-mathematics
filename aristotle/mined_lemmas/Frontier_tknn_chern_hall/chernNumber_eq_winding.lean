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

theorem chernNumber_eq_winding (L : ℝ) (n : ℤ) (hL : 0 < L)
    (A₁ A₂ D₁ D₂ : ℝ → ℝ → ℝ)
    (hA₂ : Continuous fun p : ℝ × ℝ => A₂ p.1 p.2)
    (hD₁ : Continuous fun p : ℝ × ℝ => D₁ p.1 p.2)
    (hD₂ : Continuous fun p : ℝ × ℝ => D₂ p.1 p.2)
    (hdx : ∀ x y : ℝ, HasDerivAt (fun t => A₂ t y) (D₂ x y) x)
    (hdy : ∀ x y : ℝ, HasDerivAt (fun t => A₁ x t) (D₁ x y) y)
    (hper : ∀ x : ℝ, A₁ x L = A₁ x 0)
    (hwind : ∀ y : ℝ, A₂ L y - A₂ 0 y = 2 * Real.pi * (n : ℝ) / L) :
    chernNumber A₁ A₂ L = (n : ℝ) := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hLne : L ≠ 0 := ne_of_gt hL
  rw [chernNumber, integral_berryCurvature_eq_boundary A₁ A₂ D₁ D₂ L hL.le hA₂ hD₁ hD₂ hdx hdy]
  have h1 : (∫ y in (0:ℝ)..L, (A₂ L y - A₂ 0 y)) = L * (2 * Real.pi * (n : ℝ) / L) := by
    rw [intervalIntegral.integral_congr (g := fun _ => 2 * Real.pi * (n : ℝ) / L)
      (fun y _ => hwind y)]
    simp
    ring
  have h2 : (∫ x in (0:ℝ)..L, (A₁ x L - A₁ x 0)) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ)) (fun x _ => by simp [hper x])]
    simp
  rw [h1, h2]
  field_simp
  ring

/-- **TKNN: the integer quantum Hall conductance is a Chern number times `e²/h`.**
For a band whose Berry connection on the Brillouin torus has transition function of winding
number `n`, the Kubo–TKNN Hall conductance equals `n · e²/h`. -/
