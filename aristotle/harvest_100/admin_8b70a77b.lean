/-
# Berry Phase Quantized
Category: Frontier Physics
Target: Frontier.berry_phase_quantized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

open MeasureTheory Set intervalIntegral
open scoped Interval

/-- The Berry curvature `F = ∂₁A₂ - ∂₂A₁` of a Berry connection with components
`A₁, A₂ : ℝ × ℝ → ℝ` on a two-dimensional parameter space. -/
noncomputable def berryCurvature (A₁ A₂ : ℝ × ℝ → ℝ) (x : ℝ × ℝ) : ℝ :=
  fderiv ℝ A₂ x (1, 0) - fderiv ℝ A₁ x (0, 1)

/-- The Berry phase accumulated along the closed rectangular loop with corners
`(a₁, a₂)`, `(b₁, a₂)`, `(b₁, b₂)`, `(a₁, b₂)`, traversed counterclockwise:
`∮ A · dl`. -/
noncomputable def berryPhaseLoop (A₁ A₂ : ℝ × ℝ → ℝ) (a₁ a₂ b₁ b₂ : ℝ) : ℝ :=
  ((∫ x in a₁..b₁, A₁ (x, a₂)) + ∫ y in a₂..b₂, A₂ (b₁, y)) -
    ((∫ x in a₁..b₁, A₁ (x, b₂)) + ∫ y in a₂..b₂, A₂ (a₁, y))

/-- The Berry curvature of a `C¹` Berry connection is continuous. -/
theorem continuous_berryCurvature {A₁ A₂ : ℝ × ℝ → ℝ}
    (h₁ : ContDiff ℝ 1 A₁) (h₂ : ContDiff ℝ 1 A₂) :
    Continuous (berryCurvature A₁ A₂) := by
  have c₁ : Continuous fun x : ℝ × ℝ => fderiv ℝ A₁ x :=
    h₁.continuous_fderiv one_ne_zero
  have c₂ : Continuous fun x : ℝ × ℝ => fderiv ℝ A₂ x :=
    h₂.continuous_fderiv one_ne_zero
  exact (c₂.clm_apply continuous_const).sub (c₁.clm_apply continuous_const)

/-- **Berry phase from Berry curvature.**  For a `C¹` Berry connection `(A₁, A₂)` on a
two-dimensional parameter space, the Berry phase around the closed rectangular loop with
corners `(a₁, a₂)` and `(b₁, b₂)` equals the integral of the Berry curvature
`F = ∂₁A₂ - ∂₂A₁` over the enclosed rectangle (Stokes' theorem in the plane). -/
theorem berry_phase_quantized (A₁ A₂ : ℝ × ℝ → ℝ)
    (h₁ : ContDiff ℝ 1 A₁) (h₂ : ContDiff ℝ 1 A₂) (a₁ a₂ b₁ b₂ : ℝ) :
    berryPhaseLoop A₁ A₂ a₁ a₂ b₁ b₂ =
      ∫ x in a₁..b₁, ∫ y in a₂..b₂, berryCurvature A₁ A₂ (x, y) := by
  have hd₁ : Differentiable ℝ A₁ := h₁.differentiable one_ne_zero
  have hd₂ : Differentiable ℝ A₂ := h₂.differentiable one_ne_zero
  set g : ℝ × ℝ → ℝ := fun x => -A₁ x with hg
  set f' : ℝ × ℝ → (ℝ × ℝ →L[ℝ] ℝ) := fun x => fderiv ℝ A₂ x with hf'
  set g' : ℝ × ℝ → (ℝ × ℝ →L[ℝ] ℝ) := fun x => -fderiv ℝ A₁ x with hgg'
  have hHcf : ContinuousOn A₂ ([[a₁, b₁]] ×ˢ [[a₂, b₂]]) := hd₂.continuous.continuousOn
  have hHcg : ContinuousOn g ([[a₁, b₁]] ×ˢ [[a₂, b₂]]) := hd₁.continuous.neg.continuousOn
  have hHdf : ∀ x ∈ Ioo (min a₁ b₁) (max a₁ b₁) ×ˢ Ioo (min a₂ b₂) (max a₂ b₂),
      HasFDerivAt A₂ (f' x) x := fun x _ => (hd₂ x).hasFDerivAt
  have hHdg : ∀ x ∈ Ioo (min a₁ b₁) (max a₁ b₁) ×ˢ Ioo (min a₂ b₂) (max a₂ b₂),
      HasFDerivAt g (g' x) x := fun x _ => ((hd₁ x).hasFDerivAt).neg
  have hcurv : Continuous (berryCurvature A₁ A₂) := continuous_berryCurvature h₁ h₂
  have hfun : (fun x : ℝ × ℝ => f' x (1, 0) + g' x (0, 1)) = berryCurvature A₁ A₂ := by
    funext x
    simp [hf', hgg', berryCurvature, sub_eq_add_neg]
  have hHi : IntegrableOn (fun x : ℝ × ℝ => f' x (1, 0) + g' x (0, 1))
      ([[a₁, b₁]] ×ˢ [[a₂, b₂]]) := by
    rw [hfun]
    exact hcurv.continuousOn.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)
  have key := MeasureTheory.integral2_divergence_prod_of_hasFDerivAt A₂ g f' g'
    a₁ a₂ b₁ b₂ hHcf hHcg hHdf hHdg hHi
  have hpt : ∀ x y : ℝ, f' (x, y) (1, 0) + g' (x, y) (0, 1) = berryCurvature A₁ A₂ (x, y) :=
    fun x y => congrFun hfun (x, y)
  simp only [hpt] at key
  rw [key, berryPhaseLoop]
  simp only [hg, intervalIntegral.integral_neg]
  ring

/-- If the Berry curvature vanishes identically (a flat, i.e. pure-gauge, Berry connection),
then the Berry phase around any closed rectangular loop is zero: the trivial (`n = 0`)
case of Berry phase quantization. -/
theorem berry_phase_eq_zero_of_curvature_eq_zero (A₁ A₂ : ℝ × ℝ → ℝ)
    (h₁ : ContDiff ℝ 1 A₁) (h₂ : ContDiff ℝ 1 A₂)
    (hF : ∀ x : ℝ × ℝ, berryCurvature A₁ A₂ x = 0) (a₁ a₂ b₁ b₂ : ℝ) :
    berryPhaseLoop A₁ A₂ a₁ a₂ b₁ b₂ = 0 := by
  rw [berry_phase_quantized A₁ A₂ h₁ h₂ a₁ a₂ b₁ b₂]
  simp [hF]

end Frontier

