/-
# Hairer KPZ
Category: Frontier — Fields Medal Work
Target: Frontier.hairer_KPZ
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Hairer KPZ
Category: Frontier — Fields Medal Work
Target: Frontier.hairer_KPZ
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

/-! ## Space-time partial derivatives

We work with real functions `f : ℝ → ℝ → ℝ` of a time variable and a (one dimensional)
space variable. -/

/-- Partial derivative in the time variable. -/

theorem isKPZSolution_explicit (g : ℝ → ℝ) (hg : Continuous g) (a : ℝ) :
    SpaceTimeReg (fun t x => a * x + a ^ 2 * t + ∫ s in (0 : ℝ)..t, g s) ∧
      IsKPZSolution (fun t _ => g t)
        (fun t x => a * x + a ^ 2 * t + ∫ s in (0 : ℝ)..t, g s) := by
  set h : ℝ → ℝ → ℝ := fun t x => a * x + a ^ 2 * t + ∫ s in (0 : ℝ)..t, g s with hh
  have hI : ∀ u : ℝ, HasDerivAt (fun v : ℝ => ∫ s in (0 : ℝ)..v, g s) (g u) u := fun u =>
    intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable 0 u)
      (hg.stronglyMeasurableAtFilter _ _) hg.continuousAt
  have htime : ∀ t x : ℝ, HasDerivAt (fun s : ℝ => h s x) (a ^ 2 + g t) t := by
    intro t x
    have : HasDerivAt (fun s : ℝ => a * x + (a ^ 2 * s + ∫ u in (0 : ℝ)..s, g u))
        (0 + (a ^ 2 * 1 + g t)) t :=
      (hasDerivAt_const t (a * x)).add (((hasDerivAt_id t).const_mul (a ^ 2)).add (hI t))
    simpa [hh, add_assoc] using this
  have hspace : ∀ t x : ℝ, HasDerivAt (fun y : ℝ => h t y) a x := by
    intro t x
    have : HasDerivAt (fun y : ℝ => a * y + (a ^ 2 * t + ∫ u in (0 : ℝ)..t, g u)) (a * 1 + 0) x :=
      ((hasDerivAt_id x).const_mul a).add (hasDerivAt_const x _)
    simpa [hh, add_assoc] using this
  have hdx : ∀ t x : ℝ, dx h t x = a := fun t x => (hspace t x).deriv
  have hreg : SpaceTimeReg h := by
    refine ⟨fun t x => (htime t x).differentiableAt, fun t x => (hspace t x).differentiableAt,
      fun t x => ?_⟩
    have key : (fun y : ℝ => dx h t y) = fun _ : ℝ => a := by
      funext y; exact hdx t y
    rw [key]
    exact differentiableAt_const a
  refine ⟨hreg, ?_⟩
  intro t x
  have hdxdx : dx (dx h) t x = 0 := by
    have key : (fun y : ℝ => dx h t y) = fun _ : ℝ => a := by
      funext y; exact hdx t y
    rw [dx_apply, key, deriv_const]
  rw [dt_apply, (htime t x).deriv, hdxdx, hdx t x]
  ring

/-! ## The base case: the fundamental solution of the linear equation -/

/-- The heat kernel `(4πt)^(-1/2) exp (-x²/(4t))` for `t > 0`, extended by `0` for `t ≤ 0`. -/
