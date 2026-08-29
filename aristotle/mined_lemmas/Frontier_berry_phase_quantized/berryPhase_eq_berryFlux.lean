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
open scoped Classical

open Set MeasureTheory

namespace Frontier

/-- The **Berry connection** is modelled as a real one-form on a two-dimensional parameter
space, i.e. a map `A : ℝ × ℝ → ℝ × ℝ` whose value `A p = (A₁ p, A₂ p)` gives the components
of the form `A₁ dx + A₂ dy` at the parameter point `p`. -/
abbrev BerryConnection := ℝ × ℝ → ℝ × ℝ

/-- The **Berry curvature** of a Berry connection `A` at a parameter point `p`:
`F = ∂₁ A₂ - ∂₂ A₁`, the exterior derivative of the connection one-form. -/

theorem berryPhase_eq_berryFlux (A : BerryConnection) (a₁ a₂ b₁ b₂ : ℝ)
    (h1 : Differentiable ℝ (fun q => (A q).1))
    (h2 : Differentiable ℝ (fun q => (A q).2))
    (Hi : IntegrableOn (berryCurvature A) (uIcc a₁ b₁ ×ˢ uIcc a₂ b₂)) :
    berryPhase A a₁ a₂ b₁ b₂ = berryFlux A a₁ a₂ b₁ b₂ := by
  have key := MeasureTheory.integral2_divergence_prod_of_hasFDerivAt
    (E := ℝ) (fun q => (A q).2) (fun q => -(A q).1)
    (fun p => fderiv ℝ (fun q => (A q).2) p) (fun p => -fderiv ℝ (fun q => (A q).1) p)
    a₁ a₂ b₁ b₂
    (h2.continuous.continuousOn) ((h1.continuous.neg).continuousOn)
    (fun x _ => (h2 x).hasFDerivAt)
    (fun x _ => ((h1 x).hasFDerivAt).neg)
    (by
      refine Hi.congr_fun ?_ (measurableSet_uIcc.prod measurableSet_uIcc)
      intro p _
      simp [berryCurvature, sub_eq_add_neg])
  simp only [ContinuousLinearMap.neg_apply] at key
  rw [berryPhase, berryFlux]
  rw [show (fun (x : ℝ) => ∫ y in a₂..b₂, berryCurvature A (x, y)) =
      fun (x : ℝ) => ∫ y in a₂..b₂,
        (fderiv ℝ (fun q => (A q).2) (x, y)) (1, 0) -
          (fderiv ℝ (fun q => (A q).1) (x, y)) (0, 1) from rfl]
  simp only [sub_eq_add_neg] at key ⊢
  rw [key]
  simp only [intervalIntegral.integral_neg]
  ring

/-- **Berry phase quantization.**  If the flux of the Berry curvature through the rectangle is
an integer multiple of `2π` — the quantization condition — then the Berry phase accumulated
around the boundary loop is that same integer multiple of `2π`. -/
