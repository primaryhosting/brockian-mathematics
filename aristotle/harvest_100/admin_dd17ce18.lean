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

open MeasureTheory Set intervalIntegral

/-- The Berry connection of a family of quantum states `ψ : ℝ × ℝ → H` over a two–dimensional
parameter space, given in components by `A_j (R) = Im ⟪ψ R, ∂_j ψ R⟫`. -/
noncomputable def berryConnection {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ψ : ℝ × ℝ → H) (p : ℝ × ℝ) : ℝ × ℝ :=
  ((inner ℂ (ψ p) (fderiv ℝ ψ p (1, 0)) : ℂ).im,
    (inner ℂ (ψ p) (fderiv ℝ ψ p (0, 1)) : ℂ).im)

/-- The Berry curvature `F = ∂₁ A₂ - ∂₂ A₁` of a Berry connection `A : ℝ × ℝ → ℝ × ℝ`
on a two–dimensional parameter space. -/
noncomputable def berryCurvature (A : ℝ × ℝ → ℝ × ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun x : ℝ => (A (x, p.2)).2) p.1 - deriv (fun y : ℝ => (A (p.1, y)).1) p.2

/-- The Berry phase accumulated along the (counterclockwise) boundary of the rectangle with
corners `(a₁, a₂)` and `(b₁, b₂)`, i.e. the loop integral `∮ A · dl` of the Berry connection. -/
noncomputable def berryPhaseRect (A : ℝ × ℝ → ℝ × ℝ) (a₁ a₂ b₁ b₂ : ℝ) : ℝ :=
  ((∫ x in a₁..b₁, (A (x, a₂)).1) + ∫ y in a₂..b₂, (A (b₁, y)).2) -
    ((∫ x in a₁..b₁, (A (x, b₂)).1) + ∫ y in a₂..b₂, (A (a₁, y)).2)

/-- A partial derivative in the first variable, expressed through the total derivative. -/
private lemma deriv_fst_eq {f : ℝ × ℝ → ℝ} (hf : Differentiable ℝ f) (x y : ℝ) :
    deriv (fun x : ℝ => f (x, y)) x = fderiv ℝ f (x, y) (1, 0) := by
  have h : HasDerivAt (fun x : ℝ => f (x, y)) (fderiv ℝ f (x, y) (1, 0)) x := by
    have h₁ : HasDerivAt (fun x : ℝ => (x, y)) ((1 : ℝ), (0 : ℝ)) x :=
      (hasDerivAt_id x).prodMk (hasDerivAt_const x y)
    exact (hf (x, y)).hasFDerivAt.comp_hasDerivAt x h₁
  exact h.deriv

/-- A partial derivative in the second variable, expressed through the total derivative. -/
private lemma deriv_snd_eq {f : ℝ × ℝ → ℝ} (hf : Differentiable ℝ f) (x y : ℝ) :
    deriv (fun y : ℝ => f (x, y)) y = fderiv ℝ f (x, y) (0, 1) := by
  have h : HasDerivAt (fun y : ℝ => f (x, y)) (fderiv ℝ f (x, y) (0, 1)) y := by
    have h₁ : HasDerivAt (fun y : ℝ => (x, y)) ((0 : ℝ), (1 : ℝ)) y :=
      (hasDerivAt_const y x).prodMk (hasDerivAt_id y)
    exact (hf (x, y)).hasFDerivAt.comp_hasDerivAt y h₁
  exact h.deriv

/-- **Berry phase = flux of the Berry curvature.**

For a continuously differentiable Berry connection `A` on a two–dimensional parameter space, the
Berry phase around the closed rectangular loop with corners `(a₁, a₂)` and `(b₁, b₂)` equals the
integral of the Berry curvature `F = ∂₁A₂ - ∂₂A₁` over the enclosed region.

This is Green's theorem; it is deduced from Mathlib's divergence theorem in the plane,
`MeasureTheory.integral2_divergence_prod_of_hasFDerivAt`. -/
theorem berry_phase_quantized (A : ℝ × ℝ → ℝ × ℝ) (hA : ContDiff ℝ 1 A) (a₁ a₂ b₁ b₂ : ℝ) :
    berryPhaseRect A a₁ a₂ b₁ b₂ = ∫ x in a₁..b₁, ∫ y in a₂..b₂, berryCurvature A (x, y) := by
  set f : ℝ × ℝ → ℝ := fun p => (A p).2 with hf_def
  set g : ℝ × ℝ → ℝ := fun p => -(A p).1 with hg_def
  have hfC : ContDiff ℝ 1 f := hA.snd
  have hgC : ContDiff ℝ 1 g := hA.fst.neg
  have hfD : Differentiable ℝ f := hfC.differentiable (by norm_num)
  have hgD : Differentiable ℝ g := hgC.differentiable (by norm_num)
  set f' : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℝ := fderiv ℝ f with hf'_def
  set g' : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℝ := fderiv ℝ g with hg'_def
  -- the integrand of the divergence theorem is the Berry curvature
  have hdiv : ∀ x y : ℝ, f' (x, y) (1, 0) + g' (x, y) (0, 1) = berryCurvature A (x, y) := by
    intro x y
    have h₁ : f' (x, y) (1, 0) = deriv (fun x : ℝ => (A (x, y)).2) x :=
      (deriv_fst_eq hfD x y).symm
    have h₂ : g' (x, y) (0, 1) = deriv (fun y : ℝ => -(A (x, y)).1) y :=
      (deriv_snd_eq hgD x y).symm
    have h₃ : deriv (fun y : ℝ => -(A (x, y)).1) y = -deriv (fun y : ℝ => (A (x, y)).1) y := by
      simp
    rw [h₁, h₂, h₃, berryCurvature]
    ring
  -- continuity of the derivatives
  have hcont : Continuous fun p : ℝ × ℝ => f' p (1, 0) + g' p (0, 1) := by
    have h₁ : Continuous f' := hfC.continuous_fderiv (by norm_num)
    have h₂ : Continuous g' := hgC.continuous_fderiv (by norm_num)
    exact (h₁.clm_apply continuous_const).add (h₂.clm_apply continuous_const)
  have Hi : IntegrableOn (fun p : ℝ × ℝ => f' p (1, 0) + g' p (0, 1))
      (Set.uIcc a₁ b₁ ×ˢ Set.uIcc a₂ b₂) :=
    (hcont.continuousOn).integrableOn_compact
      ((isCompact_uIcc).prod (isCompact_uIcc))
  have key := MeasureTheory.integral2_divergence_prod_of_hasFDerivAt f g f' g' a₁ a₂ b₁ b₂
    (hfC.continuous.continuousOn) (hgC.continuous.continuousOn)
    (fun x _ => (hfD x).hasFDerivAt) (fun x _ => (hgD x).hasFDerivAt) Hi
  have hleft : (∫ x in a₁..b₁, ∫ y in a₂..b₂, f' (x, y) (1, 0) + g' (x, y) (0, 1)) =
      ∫ x in a₁..b₁, ∫ y in a₂..b₂, berryCurvature A (x, y) := by
    refine intervalIntegral.integral_congr ?_
    intro x _
    exact intervalIntegral.integral_congr fun y _ => hdiv x y
  rw [hleft] at key
  rw [key, berryPhaseRect, hf_def, hg_def]
  simp only [intervalIntegral.integral_neg]
  ring

/-- Specialization to a genuine family of quantum states: whenever the Berry connection
`A_j = Im ⟪ψ, ∂_j ψ⟫` of a state family `ψ` is continuously differentiable, the Berry phase
around a rectangular loop is the flux of the Berry curvature through it. -/
theorem berry_phase_quantized_of_states {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (ψ : ℝ × ℝ → H) (hψ : ContDiff ℝ 1 (berryConnection ψ))
    (a₁ a₂ b₁ b₂ : ℝ) :
    berryPhaseRect (berryConnection ψ) a₁ a₂ b₁ b₂ =
      ∫ x in a₁..b₁, ∫ y in a₂..b₂, berryCurvature (berryConnection ψ) (x, y) :=
  berry_phase_quantized _ hψ a₁ a₂ b₁ b₂

end Frontier

