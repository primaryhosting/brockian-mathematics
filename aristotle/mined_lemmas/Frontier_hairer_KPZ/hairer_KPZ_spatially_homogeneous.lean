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

open scoped Real

namespace Frontier

/-! ## Space-time functions and partial derivatives

A space-time function is modelled as `u : ℝ → ℝ → ℝ`, where `u t x` is its value at time `t`
and space point `x`. -/

/-- Time derivative of a space-time function. -/

theorem hairer_KPZ_spatially_homogeneous (xi : ℝ → ℝ) (hxi : Continuous xi) (a : ℝ) :
    ∃! f : ℝ → ℝ, (Differentiable ℝ f ∧ f 0 = a) ∧
      IsKPZSolution (fun t _ => xi t) (fun t _ => f t) := by
  set F : ℝ → ℝ := fun t => a + ∫ s in (0 : ℝ)..t, xi s with hF
  have hFderiv : ∀ t, HasDerivAt F (xi t) t := by
    intro t
    have h := intervalIntegral.integral_hasDerivAt_right
      (hxi.intervalIntegrable 0 t)
      (hxi.stronglyMeasurableAtFilter _ _) hxi.continuousAt
    simpa [hF] using h.const_add a
  have hFdiff : Differentiable ℝ F := fun t => (hFderiv t).differentiableAt
  refine ⟨F, ⟨⟨hFdiff, by simp [hF]⟩, (isKPZSolution_const_in_space_iff xi F).2
      (fun t => (hFderiv t).deriv)⟩, ?_⟩
  rintro g ⟨⟨hgdiff, hg0⟩, hg⟩
  have hgd : ∀ t, deriv g t = xi t := (isKPZSolution_const_in_space_iff xi g).1 hg
  have hconst : ∀ t, (g - F) t = (g - F) 0 := by
    intro t
    refine is_const_of_deriv_eq_zero (hgdiff.sub hFdiff) (fun s => ?_) t 0
    rw [deriv_sub (hgdiff s) (hFdiff s), hgd s, (hFderiv s).deriv, sub_self]
  funext t
  have h := hconst t
  simp only [Pi.sub_apply, hg0, hF] at h
  simp only [hF]
  simp at h ⊢
  linarith [h]

end Frontier

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

