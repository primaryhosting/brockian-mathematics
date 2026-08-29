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

/-
# Berry Phase Quantized
Category: Frontier Physics
Target: Frontier.berry_phase_quantized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped Real Interval
open MeasureTheory Set

namespace Frontier

/-- The Berry curvature of a Berry connection `A : ℝ × ℝ → ℝ × ℝ` on a two–dimensional
parameter space: `F = ∂₁ A₂ - ∂₂ A₁`. -/
noncomputable def berryCurvature (A : ℝ × ℝ → ℝ × ℝ) (p : ℝ × ℝ) : ℝ :=
  fderiv ℝ (fun q => (A q).2) p (1, 0) - fderiv ℝ (fun q => (A q).1) p (0, 1)

/-- The Berry phase accumulated along the (counterclockwise) rectangular loop with corners
`(a₁, a₂)`, `(b₁, a₂)`, `(b₁, b₂)`, `(a₁, b₂)`, i.e. the line integral `∮ A · dl`. -/
noncomputable def berryPhase (A : ℝ × ℝ → ℝ × ℝ) (a₁ a₂ b₁ b₂ : ℝ) : ℝ :=
  ((∫ x in a₁..b₁, (A (x, a₂)).1) + ∫ y in a₂..b₂, (A (b₁, y)).2) -
    ((∫ x in a₁..b₁, (A (x, b₂)).1) + ∫ y in a₂..b₂, (A (a₁, y)).2)

/-- **Berry phase = flux of the Berry curvature.**

For a continuously differentiable Berry connection `A` on a two–dimensional parameter space,
the Berry phase around a closed (rectangular) loop equals the integral of the Berry curvature
over the enclosed region. -/
theorem berry_phase_quantized (A : ℝ × ℝ → ℝ × ℝ) (hA : ContDiff ℝ 1 A) (a₁ a₂ b₁ b₂ : ℝ) :
    berryPhase A a₁ a₂ b₁ b₂ = ∫ x in a₁..b₁, ∫ y in a₂..b₂, berryCurvature A (x, y) := by
  set A₁ : ℝ × ℝ → ℝ := fun q => (A q).1 with hA₁def
  set A₂ : ℝ × ℝ → ℝ := fun q => (A q).2 with hA₂def
  have hcd₁ : ContDiff ℝ 1 A₁ := contDiff_fst.comp hA
  have hcd₂ : ContDiff ℝ 1 A₂ := contDiff_snd.comp hA
  set g : ℝ × ℝ → ℝ := fun q => -A₁ q with hgdef
  have hcdg : ContDiff ℝ 1 g := hcd₁.neg
  -- derivatives
  have hdf : ∀ x : ℝ × ℝ, HasFDerivAt A₂ (fderiv ℝ A₂ x) x := fun x =>
    (hcd₂.differentiable (by norm_num) x).hasFDerivAt
  have hdg : ∀ x : ℝ × ℝ, HasFDerivAt g (fderiv ℝ g x) x := fun x =>
    (hcdg.differentiable (by norm_num) x).hasFDerivAt
  have hcontf' : Continuous fun x : ℝ × ℝ => fderiv ℝ A₂ x := hcd₂.continuous_fderiv (by norm_num)
  have hcontg' : Continuous fun x : ℝ × ℝ => fderiv ℝ g x := hcdg.continuous_fderiv (by norm_num)
  have hInt : IntegrableOn
      (fun x : ℝ × ℝ => fderiv ℝ A₂ x (1, 0) + fderiv ℝ g x (0, 1))
      ([[a₁, b₁]] ×ˢ [[a₂, b₂]]) :=
    ContinuousOn.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)
      (((hcontf'.clm_apply continuous_const).add
        (hcontg'.clm_apply continuous_const)).continuousOn)
  have key := MeasureTheory.integral2_divergence_prod_of_hasFDerivAt A₂ g
    (fun x => fderiv ℝ A₂ x) (fun x => fderiv ℝ g x) a₁ a₂ b₁ b₂
    (hcd₂.continuous.continuousOn) (hcdg.continuous.continuousOn)
    (fun x _ => hdf x) (fun x _ => hdg x) hInt
  -- identify the two sides
  have hgd : ∀ x : ℝ × ℝ, fderiv ℝ g x (0, 1) = -(fderiv ℝ A₁ x (0, 1)) := by
    intro x
    have : fderiv ℝ g x = -fderiv ℝ A₁ x :=
      fderiv_neg (f := A₁) (x := x)
    rw [this]
    simp
  have hcurv : ∀ x y : ℝ, berryCurvature A (x, y)
      = fderiv ℝ A₂ (x, y) (1, 0) + fderiv ℝ g (x, y) (0, 1) := by
    intro x y
    rw [hgd]
    simp [berryCurvature, hA₁def, hA₂def, sub_eq_add_neg]
  calc berryPhase A a₁ a₂ b₁ b₂
      = (((∫ x in a₁..b₁, g (x, b₂)) - ∫ x in a₁..b₁, g (x, a₂)) + ∫ y in a₂..b₂, A₂ (b₁, y)) -
          ∫ y in a₂..b₂, A₂ (a₁, y) := by
        simp only [berryPhase, hgdef, hA₁def, hA₂def, intervalIntegral.integral_neg]
        ring
    _ = ∫ x in a₁..b₁, ∫ y in a₂..b₂, fderiv ℝ A₂ (x, y) (1, 0) + fderiv ℝ g (x, y) (0, 1) :=
        key.symm
    _ = ∫ x in a₁..b₁, ∫ y in a₂..b₂, berryCurvature A (x, y) := by
        simp only [hcurv]

/-- The standard symmetric-gauge Berry connection with unit curvature. -/
noncomputable def symmetricConnection (p : ℝ × ℝ) : ℝ × ℝ := (-p.2 / 2, p.1 / 2)

/-- The symmetric gauge connection has constant Berry curvature `1`. -/
theorem berryCurvature_symmetricConnection (p : ℝ × ℝ) :
    berryCurvature symmetricConnection p = 1 := by
  have h₂ : (fun q : ℝ × ℝ => (symmetricConnection q).2) = fun q : ℝ × ℝ => q.1 / 2 := rfl
  have h₁ : (fun q : ℝ × ℝ => (symmetricConnection q).1) = fun q : ℝ × ℝ => -q.2 / 2 := rfl
  rw [berryCurvature, h₁, h₂]
  have e₂ : fderiv ℝ (fun q : ℝ × ℝ => q.1 / 2) p = (1 / 2 : ℝ) • (ContinuousLinearMap.fst ℝ ℝ ℝ) := by
    have : (fun q : ℝ × ℝ => q.1 / 2) = fun q : ℝ × ℝ => (1 / 2 : ℝ) * q.1 := by
      funext q; ring
    rw [this]
    rw [fderiv_const_mul (by fun_prop) _]
    · simp [fderiv_fst]
  have e₁ : fderiv ℝ (fun q : ℝ × ℝ => -q.2 / 2) p
      = -((1 / 2 : ℝ) • (ContinuousLinearMap.snd ℝ ℝ ℝ)) := by
    have : (fun q : ℝ × ℝ => -q.2 / 2) = fun q : ℝ × ℝ => (-(1 / 2 : ℝ)) * q.2 := by
      funext q; ring
    rw [this]
    rw [fderiv_const_mul (by fun_prop) _]
    · simp [fderiv_snd]
  rw [e₁, e₂]
  norm_num

/-- Concrete instance: for the symmetric gauge connection the Berry phase around a rectangular
loop equals the enclosed area. -/
theorem berryPhase_symmetricConnection (a₁ a₂ b₁ b₂ : ℝ) :
    berryPhase symmetricConnection a₁ a₂ b₁ b₂ = (b₁ - a₁) * (b₂ - a₂) := by
  have hA : ContDiff ℝ 1 symmetricConnection := by
    apply ContDiff.prodMk
    · exact ((contDiff_snd.neg).div_const 2)
    · exact (contDiff_fst.div_const 2)
  rw [berry_phase_quantized symmetricConnection hA a₁ a₂ b₁ b₂]
  simp [berryCurvature_symmetricConnection]
  ring

/-- Quantization instance: over the rectangle `[0, 2π] × [0, n]` the Berry phase of the
symmetric-gauge connection is exactly the quantized value `2π n`. -/
theorem berryPhase_symmetricConnection_quantized (n : ℕ) :
    berryPhase symmetricConnection 0 0 (2 * π) n = 2 * π * n := by
  rw [berryPhase_symmetricConnection]
  ring

end Frontier

