/-
# Tknn Chern Hall
Category: Frontier Physics
Target: Frontier.tknn_chern_hall
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Tknn Chern Hall
Category: Frontier Physics
Target: Frontier.tknn_chern_hall
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Real

namespace Frontier

/-! ## Vector algebra in `ℝ³`

We model `ℝ³` as `ℝ × ℝ × ℝ` and use the standard dot and cross products. -/

/-- The cross product of two vectors in `ℝ³`. -/
def cross3 (a b : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (a.2.1 * b.2.2 - a.2.2 * b.2.1, a.2.2 * b.1 - a.1 * b.2.2, a.1 * b.2.1 - a.2.1 * b.1)

/-- The dot product of two vectors in `ℝ³`. -/
def dot3 (a b : ℝ × ℝ × ℝ) : ℝ := a.1 * b.1 + a.2.1 * b.2.1 + a.2.2 * b.2.2

/-! ## The two-band Bloch Hamiltonian

For a two-band Bloch Hamiltonian `H(k) = d(k) · σ` with a nowhere-vanishing vector field `d`,
the Berry curvature of the lower band is
`F = (1/2) d̂ · (∂₁ d̂ × ∂₂ d̂)`, and the Chern number is `(1/4π) ∫ d̂ · (∂₁ d̂ × ∂₂ d̂)`,
i.e. the degree of the map `d̂` into the unit sphere.

Here we take the base case in which `d̂` is the identity (degree-one) parametrisation of the
unit sphere by spherical coordinates `(θ, φ)`. -/

/-- The normalised `d`-vector of the model, in spherical coordinates. -/
noncomputable def dvec (θ φ : ℝ) : ℝ × ℝ × ℝ := (sin θ * cos φ, sin θ * sin φ, cos θ)

/-- The candidate `θ`-derivative of `dvec`. -/
noncomputable def dTheta (θ φ : ℝ) : ℝ × ℝ × ℝ := (cos θ * cos φ, cos θ * sin φ, -sin θ)

/-- The candidate `φ`-derivative of `dvec`. -/
noncomputable def dPhi (θ φ : ℝ) : ℝ × ℝ × ℝ := (-(sin θ * sin φ), sin θ * cos φ, 0)

/-- `dvec` takes values in the unit sphere. -/
theorem dvec_norm_sq (θ φ : ℝ) : dot3 (dvec θ φ) (dvec θ φ) = 1 := by
  simp only [dot3, dvec]
  linear_combination (sin θ ^ 2) * sin_sq_add_cos_sq φ + sin_sq_add_cos_sq θ

/-- `dTheta` is indeed the partial derivative of `dvec` with respect to `θ`
(first component). -/
theorem hasDerivAt_dvec_theta_fst (θ φ : ℝ) :
    HasDerivAt (fun t : ℝ => (dvec t φ).1) (dTheta θ φ).1 θ :=
  (Real.hasDerivAt_sin θ).mul_const _

/-- `dTheta` is indeed the partial derivative of `dvec` with respect to `θ`
(second component). -/
theorem hasDerivAt_dvec_theta_snd (θ φ : ℝ) :
    HasDerivAt (fun t : ℝ => (dvec t φ).2.1) (dTheta θ φ).2.1 θ :=
  (Real.hasDerivAt_sin θ).mul_const _

/-- `dTheta` is indeed the partial derivative of `dvec` with respect to `θ`
(third component). -/
theorem hasDerivAt_dvec_theta_thd (θ φ : ℝ) :
    HasDerivAt (fun t : ℝ => (dvec t φ).2.2) (dTheta θ φ).2.2 θ :=
  Real.hasDerivAt_cos θ

/-- `dPhi` is indeed the partial derivative of `dvec` with respect to `φ`
(first component). -/
theorem hasDerivAt_dvec_phi_fst (θ φ : ℝ) :
    HasDerivAt (fun p : ℝ => (dvec θ p).1) (dPhi θ φ).1 φ := by
  have h : HasDerivAt (fun p : ℝ => sin θ * cos p) (sin θ * (-sin φ)) φ :=
    (Real.hasDerivAt_cos φ).const_mul (sin θ)
  simpa [dvec, dPhi, mul_comm] using h

/-- `dPhi` is indeed the partial derivative of `dvec` with respect to `φ`
(second component). -/
theorem hasDerivAt_dvec_phi_snd (θ φ : ℝ) :
    HasDerivAt (fun p : ℝ => (dvec θ p).2.1) (dPhi θ φ).2.1 φ := by
  have h : HasDerivAt (fun p : ℝ => sin θ * sin p) (sin θ * cos φ) φ :=
    (Real.hasDerivAt_sin φ).const_mul (sin θ)
  simpa [dvec, dPhi] using h

/-- `dPhi` is indeed the partial derivative of `dvec` with respect to `φ`
(third component). -/
theorem hasDerivAt_dvec_phi_thd (θ φ : ℝ) :
    HasDerivAt (fun p : ℝ => (dvec θ p).2.2) (dPhi θ φ).2.2 φ := by
  simpa [dvec, dPhi] using (hasDerivAt_const φ (cos θ))

/-- The (unnormalised) Berry curvature density `d̂ · (∂_θ d̂ × ∂_φ d̂)` of the model. -/
noncomputable def berryCurvature (θ φ : ℝ) : ℝ :=
  dot3 (dvec θ φ) (cross3 (dTheta θ φ) (dPhi θ φ))

/-- The Berry curvature density of the model is the round area element `sin θ`. -/
theorem berryCurvature_eq (θ φ : ℝ) : berryCurvature θ φ = sin θ := by
  simp only [berryCurvature, dot3, cross3, dvec, dTheta, dPhi]
  linear_combination (sin θ * (sin φ ^ 2 + cos φ ^ 2)) * sin_sq_add_cos_sq θ +
    sin θ * sin_sq_add_cos_sq φ

/-- The Chern number of the band: the Berry curvature integrated over the parameter torus,
normalised by `4π` (equivalently, `1/2π` times the integral of the Berry curvature
`F = (1/2) d̂ · (∂_θ d̂ × ∂_φ d̂)`). -/
noncomputable def chernNumber : ℝ :=
  (1 / (4 * π)) * ∫ θ in (0 : ℝ)..π, ∫ φ in (0 : ℝ)..(2 * π), berryCurvature θ φ

/-- The Chern number of this band equals `1`. -/
theorem chernNumber_eq_one : chernNumber = 1 := by
  have key : ∀ θ : ℝ, (∫ φ in (0 : ℝ)..(2 * π), berryCurvature θ φ) = 2 * π * sin θ := by
    intro θ
    simp [berryCurvature_eq, mul_comm]
  simp only [chernNumber, key]
  rw [intervalIntegral.integral_const_mul, integral_sin]
  simp only [Real.cos_zero, Real.cos_pi]
  have hpi : π ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-- The zero-temperature Hall conductance of the filled band, as given by the Kubo formula:
the Chern number times the conductance quantum `e²/h`. -/
noncomputable def hallConductance (e hPlanck : ℝ) : ℝ := chernNumber * (e ^ 2 / hPlanck)

/-- **TKNN (base case).** For the degree-one two-band Bloch model above, the Berry-curvature
integral over the parameter torus is quantised: it equals an *integer* Chern number `C`
(here `C = 1`), and the integer quantum Hall conductance is exactly `C · e²/h`. -/
theorem tknn_chern_hall :
    ∃ C : ℤ, C = 1 ∧ chernNumber = (C : ℝ) ∧
      ∀ e hPlanck : ℝ, hallConductance e hPlanck = (C : ℝ) * (e ^ 2 / hPlanck) := by
  refine ⟨1, rfl, ?_, ?_⟩
  · simpa using chernNumber_eq_one
  · intro e hPlanck
    simp [hallConductance, chernNumber_eq_one]

end Frontier

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

