/-
# Berry Phase Quantized
Category: Frontier Physics
Target: Frontier.berry_phase_quantized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Berry Phase Quantized
Category: Frontier Physics
Target: Frontier.berry_phase_quantized
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

/-- The Berry curvature of a Berry connection one-form `A = A₁ dx + A₂ dy` on the
(two–dimensional) parameter space `ℝ × ℝ`: it is the exterior derivative
`F = ∂₁A₂ - ∂₂A₁`. -/

theorem berry_phase_quantized (A₁ A₂ : ℝ × ℝ → ℝ)
    (h₁ : ContDiff ℝ 1 A₁) (h₂ : ContDiff ℝ 1 A₂) (a₁ a₂ b₁ b₂ : ℝ) :
    berryPhase A₁ A₂ a₁ a₂ b₁ b₂ =
      ∫ x in a₁..b₁, ∫ y in a₂..b₂, berryCurvature A₁ A₂ (x, y) := by
  have hcurv : Continuous (berryCurvature A₁ A₂) := by
    have e₂ : Continuous fun p : ℝ × ℝ => fderiv ℝ A₂ p (1, 0) :=
      (h₂.continuous_fderiv one_ne_zero).clm_apply continuous_const
    have e₁ : Continuous fun p : ℝ × ℝ => fderiv ℝ A₁ p (0, 1) :=
      (h₁.continuous_fderiv one_ne_zero).clm_apply continuous_const
    simpa [berryCurvature] using e₂.sub e₁
  have hcompact : IsCompact ((Set.uIcc a₁ b₁) ×ˢ (Set.uIcc a₂ b₂)) :=
    isCompact_uIcc.prod isCompact_uIcc
  have key := MeasureTheory.integral2_divergence_prod_of_hasFDerivAt
    (E := ℝ) A₂ (fun p => -A₁ p) (fun p => fderiv ℝ A₂ p) (fun p => -(fderiv ℝ A₁ p))
    a₁ a₂ b₁ b₂
    (h₂.continuous.continuousOn) ((h₁.continuous.neg).continuousOn)
    (fun p _ => (h₂.differentiable one_ne_zero p).hasFDerivAt)
    (fun p _ => ((h₁.differentiable one_ne_zero p).hasFDerivAt).neg)
    (by
      have : MeasureTheory.IntegrableOn (berryCurvature A₁ A₂)
          ((Set.uIcc a₁ b₁) ×ˢ (Set.uIcc a₂ b₂)) :=
        hcurv.continuousOn.integrableOn_compact hcompact
      simpa [berryCurvature, sub_eq_add_neg] using this)
  simp only [berryCurvature, sub_eq_add_neg] at key ⊢
  simp only [intervalIntegral.integral_neg, ContinuousLinearMap.neg_apply] at key
  rw [key]
  simp [berryPhase, sub_eq_add_neg]
  abel

/-- A concrete instance of the theorem, witnessing that it is not vacuous: for the symmetric-gauge
Berry connection `A = (-y/2) dx + (x/2) dy`, whose Berry curvature is the constant `1`, the Berry
phase around a rectangular loop equals the enclosed area `(b₁ - a₁) * (b₂ - a₂)`. -/
