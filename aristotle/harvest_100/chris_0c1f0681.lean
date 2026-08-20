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

/-- The Berry curvature `F = ∂₁A₂ - ∂₂A₁` associated to a Berry connection with
components `A₁, A₂ : ℝ × ℝ → ℝ` on a two-dimensional parameter space. -/
noncomputable def berryCurvature (A₁ A₂ : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun x : ℝ => A₂ (x, p.2)) p.1 - deriv (fun y : ℝ => A₁ (p.1, y)) p.2

/-- The Berry phase accumulated along the (counterclockwise) boundary of the rectangle
with corners `(a₁, a₂)` and `(b₁, b₂)`, i.e. the line integral `∮ A₁ dx + A₂ dy`. -/
noncomputable def berryPhase (A₁ A₂ : ℝ × ℝ → ℝ) (a₁ a₂ b₁ b₂ : ℝ) : ℝ :=
  ((∫ x in a₁..b₁, A₁ (x, a₂)) + ∫ y in a₂..b₂, A₂ (b₁, y)) -
    ((∫ x in a₁..b₁, A₁ (x, b₂)) + ∫ y in a₂..b₂, A₂ (a₁, y))

/-- Key intermediate lemma (first partial derivative): for a continuously differentiable
function on the plane, applying the Fréchet derivative to the first basis vector computes the
partial derivative in the first variable. -/
theorem fderiv_apply_fst (f : ℝ × ℝ → ℝ) (hf : Differentiable ℝ f) (x y : ℝ) :
    fderiv ℝ f (x, y) (1, 0) = deriv (fun t : ℝ => f (t, y)) x := by
  have hline : HasFDerivAt (fun t : ℝ => (t, y)) ((ContinuousLinearMap.id ℝ ℝ).prod 0) x := by
    exact (hasFDerivAt_id x).prodMk (hasFDerivAt_const y x)
  have hcomp : HasDerivAt (fun t : ℝ => f (t, y)) (fderiv ℝ f (x, y) (1, 0)) x := by
    have := ((hf (x, y)).hasFDerivAt.comp x hline).hasDerivAt
    simpa using this
  exact (hcomp.deriv).symm

/-- Key intermediate lemma (second partial derivative): for a continuously differentiable
function on the plane, applying the Fréchet derivative to the second basis vector computes the
partial derivative in the second variable. -/
theorem fderiv_apply_snd (f : ℝ × ℝ → ℝ) (hf : Differentiable ℝ f) (x y : ℝ) :
    fderiv ℝ f (x, y) (0, 1) = deriv (fun t : ℝ => f (x, t)) y := by
  have hline : HasFDerivAt (fun t : ℝ => (x, t)) ((0 : ℝ →L[ℝ] ℝ).prod
      (ContinuousLinearMap.id ℝ ℝ)) y := by
    exact (hasFDerivAt_const x y).prodMk (hasFDerivAt_id y)
  have hcomp : HasDerivAt (fun t : ℝ => f (x, t)) (fderiv ℝ f (x, y) (0, 1)) y := by
    have := ((hf (x, y)).hasFDerivAt.comp y hline).hasDerivAt
    simpa using this
  exact (hcomp.deriv).symm

/-- The Berry curvature, expressed via Fréchet derivatives. -/
theorem berryCurvature_eq (A₁ A₂ : ℝ × ℝ → ℝ) (h₁ : Differentiable ℝ A₁)
    (h₂ : Differentiable ℝ A₂) (p : ℝ × ℝ) :
    berryCurvature A₁ A₂ p = fderiv ℝ A₂ p (1, 0) + (-(fderiv ℝ A₁ p)) (0, 1) := by
  obtain ⟨x, y⟩ := p
  simp only [berryCurvature, ContinuousLinearMap.neg_apply]
  rw [fderiv_apply_fst A₂ h₂ x y, fderiv_apply_snd A₁ h₁ x y]
  ring

/-- **Berry phase = flux of the Berry curvature.**

For a continuously differentiable Berry connection `(A₁, A₂)` on a two-dimensional parameter
space, the Berry phase accumulated around the closed rectangular loop with corners `(a₁, a₂)`
and `(b₁, b₂)` equals the integral of the Berry curvature `F = ∂₁A₂ - ∂₂A₁` over the enclosed
region.  (This is Stokes' theorem for the Berry connection one-form; the quantization of the
Berry phase over a closed surface follows by gluing such patches.) -/
theorem berry_phase_quantized (A₁ A₂ : ℝ × ℝ → ℝ) (h₁ : ContDiff ℝ 1 A₁)
    (h₂ : ContDiff ℝ 1 A₂) (a₁ a₂ b₁ b₂ : ℝ) :
    berryPhase A₁ A₂ a₁ a₂ b₁ b₂ =
      ∫ x in a₁..b₁, ∫ y in a₂..b₂, berryCurvature A₁ A₂ (x, y) := by
  have hd₁ : Differentiable ℝ A₁ := h₁.differentiable one_ne_zero
  have hd₂ : Differentiable ℝ A₂ := h₂.differentiable one_ne_zero
  set f : ℝ × ℝ → ℝ := A₂ with hf
  set g : ℝ × ℝ → ℝ := fun p => -A₁ p with hg
  set f' : ℝ × ℝ → (ℝ × ℝ →L[ℝ] ℝ) := fun p => fderiv ℝ A₂ p with hf'
  set g' : ℝ × ℝ → (ℝ × ℝ →L[ℝ] ℝ) := fun p => -(fderiv ℝ A₁ p) with hg'
  have hcurv : ∀ p : ℝ × ℝ, f' p (1, 0) + g' p (0, 1) = berryCurvature A₁ A₂ p := fun p =>
    (berryCurvature_eq A₁ A₂ hd₁ hd₂ p).symm
  -- continuity of the curvature
  have hcont : Continuous fun p : ℝ × ℝ => f' p (1, 0) + g' p (0, 1) := by
    have c₁ : Continuous fun p : ℝ × ℝ => fderiv ℝ A₁ p := h₁.continuous_fderiv one_ne_zero
    have c₂ : Continuous fun p : ℝ × ℝ => fderiv ℝ A₂ p := h₂.continuous_fderiv one_ne_zero
    exact ((c₂.clm_apply continuous_const).add ((c₁.neg).clm_apply continuous_const))
  have hi : IntegrableOn (fun p : ℝ × ℝ => f' p (1, 0) + g' p (0, 1))
      (uIcc a₁ b₁ ×ˢ uIcc a₂ b₂) :=
    (hcont.continuousOn).integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)
  have key := MeasureTheory.integral2_divergence_prod_of_hasFDerivAt f g f' g' a₁ a₂ b₁ b₂
    (hd₂.continuous.continuousOn) ((hd₁.continuous.neg).continuousOn)
    (fun p _ => (hd₂ p).hasFDerivAt) (fun p _ => ((hd₁ p).hasFDerivAt).neg) hi
  simp only [hcurv] at key
  rw [key, berryPhase]
  simp only [hg, hf]
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_neg]
  ring

end Frontier

