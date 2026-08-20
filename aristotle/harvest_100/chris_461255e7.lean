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

open MeasureTheory intervalIntegral Set

/-- The Berry connection is modelled as a (real) `1`-form on a two–dimensional parameter space,
i.e. a map `A : ℝ × ℝ → ℝ × ℝ` assigning to each parameter point `p` the pair of components
`(A₁ p, A₂ p)` of the connection. -/
abbrev BerryConnection := ℝ × ℝ → ℝ × ℝ

/-- The Berry curvature `F = ∂₁A₂ - ∂₂A₁` of a Berry connection `A` at a parameter point `p`. -/
noncomputable def berryCurvature (A : BerryConnection) (p : ℝ × ℝ) : ℝ :=
  fderiv ℝ (fun q : ℝ × ℝ => (A q).2) p (1, 0) -
    fderiv ℝ (fun q : ℝ × ℝ => (A q).1) p (0, 1)

/-- The Berry phase accumulated along the (counterclockwise) closed rectangular loop with
corners `(a₁, a₂)`, `(b₁, a₂)`, `(b₁, b₂)`, `(a₁, b₂)`: it is the line integral
`∮ A₁ dx + A₂ dy` of the Berry connection along that loop. -/
noncomputable def berryPhase (A : BerryConnection) (a₁ a₂ b₁ b₂ : ℝ) : ℝ :=
  ((∫ x in a₁..b₁, (A (x, a₂)).1) + ∫ y in a₂..b₂, (A (b₁, y)).2) -
    ((∫ x in a₁..b₁, (A (x, b₂)).1) + ∫ y in a₂..b₂, (A (a₁, y)).2)

/-- **Berry phase = integral of the Berry curvature.**

For a continuously differentiable Berry connection `A` on a two–dimensional parameter space,
the Berry phase accumulated around the closed rectangular loop with corners `(aᵢ, bⱼ)` equals
the integral of the Berry curvature `F = ∂₁A₂ - ∂₂A₁` over the enclosed rectangle.

This is Green's theorem in the plane; the proof reduces it to Mathlib's divergence theorem
`MeasureTheory.integral2_divergence_prod_of_hasFDerivAt`. -/
theorem berry_phase_quantized (A : BerryConnection) (hA : ContDiff ℝ 1 A) (a₁ a₂ b₁ b₂ : ℝ) :
    berryPhase A a₁ a₂ b₁ b₂ = ∫ x in a₁..b₁, ∫ y in a₂..b₂, berryCurvature A (x, y) := by
  have hcd₁ : ContDiff ℝ 1 (fun q : ℝ × ℝ => (A q).1) := contDiff_fst.comp hA
  have hcd₂ : ContDiff ℝ 1 (fun q : ℝ × ℝ => (A q).2) := contDiff_snd.comp hA
  have hd₁ : ∀ x : ℝ × ℝ,
      HasFDerivAt (fun q : ℝ × ℝ => (A q).1) (fderiv ℝ (fun q : ℝ × ℝ => (A q).1) x) x :=
    fun x => (hcd₁.differentiable (by simp) x).hasFDerivAt
  have hd₂ : ∀ x : ℝ × ℝ,
      HasFDerivAt (fun q : ℝ × ℝ => (A q).2) (fderiv ℝ (fun q : ℝ × ℝ => (A q).2) x) x :=
    fun x => (hcd₂.differentiable (by simp) x).hasFDerivAt
  have hdivcont : Continuous fun x : ℝ × ℝ =>
      (fderiv ℝ (fun q : ℝ × ℝ => (A q).2) x) (1, 0) +
        (-fderiv ℝ (fun q : ℝ × ℝ => (A q).1) x) (0, 1) := by
    have h1 : Continuous fun x : ℝ × ℝ => (fderiv ℝ (fun q : ℝ × ℝ => (A q).2) x) (1, 0) :=
      (hcd₂.continuous_fderiv (by simp)).clm_apply continuous_const
    have h2 : Continuous fun x : ℝ × ℝ => (fderiv ℝ (fun q : ℝ × ℝ => (A q).1) x) (0, 1) :=
      (hcd₁.continuous_fderiv (by simp)).clm_apply continuous_const
    simpa using h1.add h2.neg
  have hcompact : IsCompact ((Set.uIcc a₁ b₁) ×ˢ (Set.uIcc a₂ b₂) : Set (ℝ × ℝ)) :=
    isCompact_uIcc.prod isCompact_uIcc
  have key := MeasureTheory.integral2_divergence_prod_of_hasFDerivAt
      (fun q : ℝ × ℝ => (A q).2) (fun q : ℝ × ℝ => -(A q).1)
      (fun x => fderiv ℝ (fun q : ℝ × ℝ => (A q).2) x)
      (fun x => -fderiv ℝ (fun q : ℝ × ℝ => (A q).1) x) a₁ a₂ b₁ b₂
      hcd₂.continuous.continuousOn (hcd₁.continuous.neg).continuousOn
      (fun x _ => hd₂ x) (fun x _ => (hd₁ x).neg)
      (hdivcont.continuousOn.integrableOn_compact hcompact)
  have hleft : (∫ x in a₁..b₁, ∫ y in a₂..b₂,
        (fderiv ℝ (fun q : ℝ × ℝ => (A q).2) (x, y)) (1, 0) +
          (-fderiv ℝ (fun q : ℝ × ℝ => (A q).1) (x, y)) (0, 1)) =
      ∫ x in a₁..b₁, ∫ y in a₂..b₂, berryCurvature A (x, y) := by
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    refine intervalIntegral.integral_congr (fun y _ => ?_)
    simp [berryCurvature, sub_eq_add_neg]
  rw [← hleft, key, berryPhase, intervalIntegral.integral_neg, intervalIntegral.integral_neg]
  ring

end Frontier

