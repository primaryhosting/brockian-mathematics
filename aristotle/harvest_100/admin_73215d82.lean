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
noncomputable def berryCurvature (A₁ A₂ : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  fderiv ℝ A₂ p (1, 0) - fderiv ℝ A₁ p (0, 1)

/-- The Berry phase accumulated along the (counterclockwise) closed rectangular loop with
corners `(a₁, a₂)`, `(b₁, a₂)`, `(b₁, b₂)`, `(a₁, b₂)`, i.e. the line integral
`∮ A₁ dx + A₂ dy` of the Berry connection along that loop. -/
noncomputable def berryPhase (A₁ A₂ : ℝ × ℝ → ℝ) (a₁ a₂ b₁ b₂ : ℝ) : ℝ :=
  (∫ x in a₁..b₁, A₁ (x, a₂)) + (∫ y in a₂..b₂, A₂ (b₁, y))
    - (∫ x in a₁..b₁, A₁ (x, b₂)) - (∫ y in a₂..b₂, A₂ (a₁, y))

/-- **Berry phase = flux of the Berry curvature.**

For a continuously differentiable Berry connection `A = A₁ dx + A₂ dy` on the parameter plane,
the Berry phase around the closed rectangular loop with corners `(a₁, a₂)` and `(b₁, b₂)` equals
the integral of the Berry curvature `F = ∂₁A₂ - ∂₂A₁` over the enclosed rectangle.

This is Stokes'/Green's theorem in the plane; it is deduced from Mathlib's divergence theorem
`MeasureTheory.integral2_divergence_prod_of_hasFDerivAt`. -/
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
theorem berryPhase_symmetric_gauge (a₁ a₂ b₁ b₂ : ℝ) :
    berryPhase (fun p : ℝ × ℝ => -p.2 / 2) (fun p : ℝ × ℝ => p.1 / 2) a₁ a₂ b₁ b₂ =
      (b₁ - a₁) * (b₂ - a₂) := by
  have hA₁ : ContDiff ℝ 1 (fun p : ℝ × ℝ => -p.2 / 2) := (contDiff_snd.neg).div_const 2
  have hA₂ : ContDiff ℝ 1 (fun p : ℝ × ℝ => p.1 / 2) := contDiff_fst.div_const 2
  have hcurv : ∀ p : ℝ × ℝ,
      berryCurvature (fun p : ℝ × ℝ => -p.2 / 2) (fun p : ℝ × ℝ => p.1 / 2) p = 1 := by
    intro p
    have h₂ : HasFDerivAt (fun q : ℝ × ℝ => q.1 / 2)
        ((2:ℝ)⁻¹ • (ContinuousLinearMap.fst ℝ ℝ ℝ)) p := by
      simpa [div_eq_inv_mul] using (hasFDerivAt_fst (𝕜 := ℝ) (p := p)).const_smul ((2:ℝ)⁻¹)
    have h₁ : HasFDerivAt (fun q : ℝ × ℝ => -q.2 / 2)
        (-((2:ℝ)⁻¹ • (ContinuousLinearMap.snd ℝ ℝ ℝ))) p := by
      simpa [div_eq_inv_mul, neg_div] using
        (((hasFDerivAt_snd (𝕜 := ℝ) (p := p)).const_smul ((2:ℝ)⁻¹)).neg)
    rw [berryCurvature, h₁.fderiv, h₂.fderiv]
    norm_num
  rw [berry_phase_quantized _ _ hA₁ hA₂]
  simp only [hcurv]
  simp
  ring

end Frontier

