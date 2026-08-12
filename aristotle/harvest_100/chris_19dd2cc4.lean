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

open MeasureTheory intervalIntegral Set

/-- The Berry connection of a smooth family of states `psi : ℝ × ℝ → H` over a two–dimensional
parameter space, evaluated in the parameter direction `v`:
`A_v(p) = Re (i ⟪ψ(p), D_v ψ(p)⟫)`.  (For a normalized family this quantity is automatically
real, so taking the real part is harmless.) -/
noncomputable def berryConnection {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (psi : ℝ × ℝ → H) (v : ℝ × ℝ) (p : ℝ × ℝ) : ℝ :=
  (Complex.I * (inner ℂ (psi p) (fderiv ℝ psi p v))).re

/-- The Berry phase accumulated along the closed loop given by the (counterclockwise) boundary of
the parameter rectangle with corners `(a₁, a₂)` and `(b₁, b₂)`, for the connection with
components `A₁, A₂`:  `∮ (A₁ dx + A₂ dy)`. -/
noncomputable def berryPhase (A₁ A₂ : ℝ × ℝ → ℝ) (a₁ a₂ b₁ b₂ : ℝ) : ℝ :=
  (∫ x in a₁..b₁, A₁ (x, a₂)) + (∫ y in a₂..b₂, A₂ (b₁, y))
    - (∫ x in a₁..b₁, A₁ (x, b₂)) - (∫ y in a₂..b₂, A₂ (a₁, y))

/-- The Berry curvature `F₁₂ = ∂₁ A₂ - ∂₂ A₁` of the connection with components `A₁, A₂`. -/
noncomputable def berryCurvature (A₁ A₂ : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  fderiv ℝ A₂ p (1, 0) - fderiv ℝ A₁ p (0, 1)

/-- **Berry phase = integral of the Berry curvature.**

For a continuously differentiable Berry connection `A = A₁ dx + A₂ dy` on a two–dimensional
parameter space, the Berry phase accumulated around the closed loop bounding the rectangle
`[a₁, b₁] × [a₂, b₂]` equals the integral of the Berry curvature `F₁₂ = ∂₁A₂ - ∂₂A₁` over the
enclosed region. -/
theorem berry_phase_quantized (A₁ A₂ : ℝ × ℝ → ℝ)
    (h₁ : ContDiff ℝ 1 A₁) (h₂ : ContDiff ℝ 1 A₂) (a₁ a₂ b₁ b₂ : ℝ) :
    berryPhase A₁ A₂ a₁ a₂ b₁ b₂ =
      ∫ x in a₁..b₁, ∫ y in a₂..b₂, berryCurvature A₁ A₂ (x, y) := by
  have hd₁ : Differentiable ℝ A₁ := h₁.differentiable (by norm_num)
  have hd₂ : Differentiable ℝ A₂ := h₂.differentiable (by norm_num)
  have hcont : Continuous fun p : ℝ × ℝ =>
      (fderiv ℝ A₂ p) (1, 0) + (-fderiv ℝ A₁ p) (0, 1) := by
    have c₁ : Continuous fun p : ℝ × ℝ => fderiv ℝ A₁ p := h₁.continuous_fderiv (by norm_num)
    have c₂ : Continuous fun p : ℝ × ℝ => fderiv ℝ A₂ p := h₂.continuous_fderiv (by norm_num)
    have e₁ : Continuous fun p : ℝ × ℝ => (fderiv ℝ A₁ p) (0, 1) :=
      c₁.clm_apply continuous_const
    have e₂ : Continuous fun p : ℝ × ℝ => (fderiv ℝ A₂ p) (1, 0) :=
      c₂.clm_apply continuous_const
    simpa [sub_eq_add_neg] using e₂.sub e₁
  have key :=
    MeasureTheory.integral2_divergence_prod_of_hasFDerivAt A₂ (fun p => -A₁ p)
      (fun p => fderiv ℝ A₂ p) (fun p => -fderiv ℝ A₁ p) a₁ a₂ b₁ b₂
      hd₂.continuous.continuousOn hd₁.continuous.neg.continuousOn
      (fun p _ => (hd₂ p).hasFDerivAt) (fun p _ => (hd₁ p).hasFDerivAt.neg)
      (hcont.continuousOn.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc))
  have hint : (∫ x in a₁..b₁, ∫ y in a₂..b₂, berryCurvature A₁ A₂ (x, y))
      = ∫ x in a₁..b₁, ∫ y in a₂..b₂,
          (fderiv ℝ A₂ (x, y)) (1, 0) + (-fderiv ℝ A₁ (x, y)) (0, 1) := by
    simp [berryCurvature, sub_eq_add_neg]
  rw [berryPhase, hint, key]
  simp only [intervalIntegral.integral_neg]
  ring

/-- The Berry phase of a smooth family of quantum states, around the closed loop bounding a
rectangle in parameter space, is the integral of its Berry curvature over that rectangle. -/
theorem berry_phase_quantized_of_states {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (psi : ℝ × ℝ → H)
    (h₁ : ContDiff ℝ 1 (berryConnection psi (1, 0)))
    (h₂ : ContDiff ℝ 1 (berryConnection psi (0, 1))) (a₁ a₂ b₁ b₂ : ℝ) :
    berryPhase (berryConnection psi (1, 0)) (berryConnection psi (0, 1)) a₁ a₂ b₁ b₂ =
      ∫ x in a₁..b₁, ∫ y in a₂..b₂,
        berryCurvature (berryConnection psi (1, 0)) (berryConnection psi (0, 1)) (x, y) :=
  berry_phase_quantized _ _ h₁ h₂ a₁ a₂ b₁ b₂

end Frontier

