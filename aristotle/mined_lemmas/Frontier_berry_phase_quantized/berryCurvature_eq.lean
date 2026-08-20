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
