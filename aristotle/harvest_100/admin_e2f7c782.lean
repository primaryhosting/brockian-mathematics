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
open scoped Interval

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

open MeasureTheory intervalIntegral Set

/-- The Berry connection is modelled as a (real) one-form on a two–dimensional parameter
space, i.e. a map `A : ℝ × ℝ → ℝ × ℝ` whose components `(A p).1`, `(A p).2` are the
components `A₁`, `A₂` of the connection at the parameter point `p`. -/
noncomputable def berryCurvature (A : ℝ × ℝ → ℝ × ℝ) (p : ℝ × ℝ) : ℝ :=
  fderiv ℝ (fun q : ℝ × ℝ => (A q).2) p (1, 0) -
    fderiv ℝ (fun q : ℝ × ℝ => (A q).1) p (0, 1)

/-- The Berry phase accumulated along the closed rectangular loop traversed
counterclockwise around the boundary of the rectangle with opposite corners
`(a₁, a₂)` and `(b₁, b₂)`: it is the line integral of the Berry connection
along that loop. -/
noncomputable def berryPhase (A : ℝ × ℝ → ℝ × ℝ) (a₁ a₂ b₁ b₂ : ℝ) : ℝ :=
  ((∫ x in a₁..b₁, (A (x, a₂)).1) + ∫ y in a₂..b₂, (A (b₁, y)).2) -
    ((∫ x in a₁..b₁, (A (x, b₂)).1) + ∫ y in a₂..b₂, (A (a₁, y)).2)

/-- **Berry phase from the Berry curvature.**
For a continuously differentiable Berry connection `A` on a two–dimensional parameter
space, the Berry phase around the closed rectangular loop bounding
`[a₁, b₁] × [a₂, b₂]` equals the integral of the Berry curvature
`F = ∂₁A₂ - ∂₂A₁` over the enclosed region. -/
theorem berry_phase_quantized (A : ℝ × ℝ → ℝ × ℝ) (hA : ContDiff ℝ 1 A)
    (a₁ a₂ b₁ b₂ : ℝ) :
    (∫ x in a₁..b₁, ∫ y in a₂..b₂, berryCurvature A (x, y)) =
      berryPhase A a₁ a₂ b₁ b₂ := by
  -- Put the statement in the form of the two–dimensional divergence (Green) theorem.
  set f : ℝ × ℝ → ℝ := fun q => (A q).2 with hf
  set g : ℝ × ℝ → ℝ := fun q => -(A q).1 with hg
  have hfC : ContDiff ℝ 1 f := contDiff_snd.comp hA
  have hgC : ContDiff ℝ 1 g := (contDiff_fst.comp hA).neg
  set f' : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ := fun p => fderiv ℝ f p with hf'
  set g' : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ := fun p => fderiv ℝ g p with hg'
  have hf'c : Continuous f' := hfC.continuous_fderiv one_ne_zero
  have hg'c : Continuous g' := hgC.continuous_fderiv one_ne_zero
  have hcont : Continuous (fun p : ℝ × ℝ => f' p (1, 0) + g' p (0, 1)) :=
    (hf'c.clm_apply continuous_const).add (hg'c.clm_apply continuous_const)
  have hcompact : IsCompact (([[a₁, b₁]] ×ˢ [[a₂, b₂]] : Set (ℝ × ℝ))) :=
    isCompact_uIcc.prod isCompact_uIcc
  have key :
      (∫ x in a₁..b₁, ∫ y in a₂..b₂, f' (x, y) (1, 0) + g' (x, y) (0, 1)) =
        (((∫ x in a₁..b₁, g (x, b₂)) - ∫ x in a₁..b₁, g (x, a₂)) +
            ∫ y in a₂..b₂, f (b₁, y)) - ∫ y in a₂..b₂, f (a₁, y) :=
    integral2_divergence_prod_of_hasFDerivAt f g f' g' a₁ a₂ b₁ b₂
      (hfC.continuous.continuousOn) (hgC.continuous.continuousOn)
      (fun x _ => (hfC.differentiable one_ne_zero x).hasFDerivAt)
      (fun x _ => (hgC.differentiable one_ne_zero x).hasFDerivAt)
      (hcont.continuousOn.integrableOn_compact hcompact)
  -- Identify the integrand with the Berry curvature.
  have hcurv : ∀ p : ℝ × ℝ, berryCurvature A p = f' p (1, 0) + g' p (0, 1) := by
    intro p
    simp only [berryCurvature, hf', hg', hf, hg, fderiv_neg,
      ContinuousLinearMap.neg_apply]
    ring
  simp only [hcurv]
  rw [key, berryPhase, hf, hg]
  simp only [intervalIntegral.integral_neg]
  ring

end Frontier

