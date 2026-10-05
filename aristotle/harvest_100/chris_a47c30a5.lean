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

/-- The Berry phase accumulated along the closed rectangular loop
`(a,c) → (b,c) → (b,d) → (a,d) → (a,c)` in a two-dimensional parameter space,
for a Berry connection with components `A₁, A₂`.  It is the line integral
`∮ A₁ dx + A₂ dy` around the boundary of the rectangle `[a,b] × [c,d]`. -/
noncomputable def berryPhaseLoop (A₁ A₂ : ℝ → ℝ → ℝ) (a b c d : ℝ) : ℝ :=
  (∫ x in a..b, A₁ x c) + (∫ y in c..d, A₂ b y)
    - (∫ x in a..b, A₁ x d) - (∫ y in c..d, A₂ a y)

/-- The flux of the Berry curvature `F = ∂₁A₂ - ∂₂A₁` through the rectangle
`[a,b] × [c,d]`, written as a difference of iterated integrals of the two
partial derivatives `F₁ = ∂₁A₂` and `F₂ = ∂₂A₁`. -/
noncomputable def berryCurvatureFlux (F₁ F₂ : ℝ → ℝ → ℝ) (a b c d : ℝ) : ℝ :=
  (∫ y in c..d, ∫ x in a..b, F₁ x y) - (∫ x in a..b, ∫ y in c..d, F₂ x y)

/-- Fundamental theorem of calculus in the first slot: integrating `∂₁A₂` in `x`
recovers the boundary values of `A₂`. -/
theorem integral_partial_one (A₂ F₁ : ℝ → ℝ → ℝ)
    (hderiv : ∀ x y : ℝ, HasDerivAt (fun t : ℝ => A₂ t y) (F₁ x y) x)
    (hcont : Continuous fun p : ℝ × ℝ => F₁ p.1 p.2) (a b y : ℝ) :
    (∫ x in a..b, F₁ x y) = A₂ b y - A₂ a y := by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x y) ?_
  exact (hcont.comp (continuous_id.prodMk continuous_const)).intervalIntegrable a b

/-- Fundamental theorem of calculus in the second slot: integrating `∂₂A₁` in `y`
recovers the boundary values of `A₁`. -/
theorem integral_partial_two (A₁ F₂ : ℝ → ℝ → ℝ)
    (hderiv : ∀ x y : ℝ, HasDerivAt (fun t : ℝ => A₁ x t) (F₂ x y) y)
    (hcont : Continuous fun p : ℝ × ℝ => F₂ p.1 p.2) (c d x : ℝ) :
    (∫ y in c..d, F₂ x y) = A₁ x d - A₁ x c := by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hderiv x y) ?_
  exact (hcont.comp (continuous_const.prodMk continuous_id)).intervalIntegrable c d

/-- **Berry phase = flux of the Berry curvature, and quantization.**

For a smooth Berry connection `A = (A₁, A₂)` on a two-dimensional parameter
space, with Berry curvature `F = ∂₁A₂ - ∂₂A₁`:

* the Berry phase around the closed rectangular loop bounding `[a,b] × [c,d]`
  equals the flux of the Berry curvature through that rectangle (Stokes/Green);
* consequently, whenever that flux is an integer multiple of `2π` (a quantized
  Chern-type flux), the Berry phase factor `exp (i γ)` equals `1`. -/
theorem berry_phase_quantized (A₁ A₂ F₁ F₂ : ℝ → ℝ → ℝ) (a b c d : ℝ)
    (hA₂ : ∀ x y : ℝ, HasDerivAt (fun t : ℝ => A₂ t y) (F₁ x y) x)
    (hA₁ : ∀ x y : ℝ, HasDerivAt (fun t : ℝ => A₁ x t) (F₂ x y) y)
    (hF₁ : Continuous fun p : ℝ × ℝ => F₁ p.1 p.2)
    (hF₂ : Continuous fun p : ℝ × ℝ => F₂ p.1 p.2)
    (hcA₁ : Continuous fun p : ℝ × ℝ => A₁ p.1 p.2)
    (hcA₂ : Continuous fun p : ℝ × ℝ => A₂ p.1 p.2) :
    berryPhaseLoop A₁ A₂ a b c d = berryCurvatureFlux F₁ F₂ a b c d ∧
      ∀ n : ℤ, berryCurvatureFlux F₁ F₂ a b c d = 2 * Real.pi * n →
        Complex.exp (Complex.I * (berryPhaseLoop A₁ A₂ a b c d : ℂ)) = 1 := by
  have hA₂b : Continuous fun y : ℝ => A₂ b y :=
    hcA₂.comp (continuous_const.prodMk continuous_id)
  have hA₂a : Continuous fun y : ℝ => A₂ a y :=
    hcA₂.comp (continuous_const.prodMk continuous_id)
  have hA₁d : Continuous fun x : ℝ => A₁ x d :=
    hcA₁.comp (continuous_id.prodMk continuous_const)
  have hA₁c : Continuous fun x : ℝ => A₁ x c :=
    hcA₁.comp (continuous_id.prodMk continuous_const)
  -- First iterated integral: flux of `∂₁A₂`.
  have h1 : (∫ y in c..d, ∫ x in a..b, F₁ x y)
      = (∫ y in c..d, A₂ b y) - (∫ y in c..d, A₂ a y) := by
    have : (∫ y in c..d, ∫ x in a..b, F₁ x y) = ∫ y in c..d, (A₂ b y - A₂ a y) := by
      refine intervalIntegral.integral_congr ?_
      intro y _
      exact integral_partial_one A₂ F₁ hA₂ hF₁ a b y
    rw [this]
    exact intervalIntegral.integral_sub (hA₂b.intervalIntegrable c d)
      (hA₂a.intervalIntegrable c d)
  -- Second iterated integral: flux of `∂₂A₁`.
  have h2 : (∫ x in a..b, ∫ y in c..d, F₂ x y)
      = (∫ x in a..b, A₁ x d) - (∫ x in a..b, A₁ x c) := by
    have : (∫ x in a..b, ∫ y in c..d, F₂ x y) = ∫ x in a..b, (A₁ x d - A₁ x c) := by
      refine intervalIntegral.integral_congr ?_
      intro x _
      exact integral_partial_two A₁ F₂ hA₁ hF₂ c d x
    rw [this]
    exact intervalIntegral.integral_sub (hA₁d.intervalIntegrable a b)
      (hA₁c.intervalIntegrable a b)
  have hstokes : berryPhaseLoop A₁ A₂ a b c d = berryCurvatureFlux F₁ F₂ a b c d := by
    unfold berryPhaseLoop berryCurvatureFlux
    rw [h1, h2]
    ring
  refine ⟨hstokes, ?_⟩
  intro n hn
  rw [hstokes, hn]
  have : ((2 * Real.pi * (n : ℝ) : ℝ) : ℂ) = (n : ℂ) * (2 * (Real.pi : ℂ)) := by
    push_cast
    ring
  rw [this]
  have hmul : Complex.I * ((n : ℂ) * (2 * (Real.pi : ℂ)))
      = (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by ring
  rw [hmul, Complex.exp_int_mul_two_pi_mul_I]

end Frontier

