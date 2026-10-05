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

import Mathlib

/-!
# Unruh Effect
Category: Frontier Phys
Target: Phys.unruh_effect
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

open Real

/-!
## The Rindler worldline

A uniformly accelerated observer with proper acceleration `a` moves on the Rindler
hyperbola, parametrised by proper time `τ`:
`t(τ) = (c/a) sinh (a τ / c)`, `x(τ) = (c²/a) cosh (a τ / c)`.
-/

/-- Minkowski time coordinate of the uniformly accelerated (Rindler) observer, as a
function of its proper time. -/
noncomputable def rindlerTime (a c τ : ℝ) : ℝ := (c / a) * Real.sinh (a * τ / c)

/-- Minkowski space coordinate of the uniformly accelerated (Rindler) observer, as a
function of its proper time. -/
noncomputable def rindlerPos (a c τ : ℝ) : ℝ := (c ^ 2 / a) * Real.cosh (a * τ / c)

variable {a c : ℝ}

private lemma hasDerivAt_arg (a c τ : ℝ) :
    HasDerivAt (fun s : ℝ => a * s / c) (a / c) τ := by
  simpa using ((hasDerivAt_id τ).const_mul a).div_const c

/-- The Minkowski time of the Rindler observer has proper-time derivative
`dt/dτ = cosh (a τ / c)`. -/
theorem hasDerivAt_rindlerTime (ha : a ≠ 0) (hc : c ≠ 0) (τ : ℝ) :
    HasDerivAt (rindlerTime a c) (Real.cosh (a * τ / c)) τ := by
  have h := (((Real.hasDerivAt_sinh (a * τ / c)).comp τ
    (hasDerivAt_arg a c τ)).const_mul (c / a))
  convert h using 1
  field_simp

/-- The Minkowski position of the Rindler observer has proper-time derivative
`dx/dτ = c · sinh (a τ / c)`. -/
theorem hasDerivAt_rindlerPos (ha : a ≠ 0) (hc : c ≠ 0) (τ : ℝ) :
    HasDerivAt (rindlerPos a c) (c * Real.sinh (a * τ / c)) τ := by
  have h := (((Real.hasDerivAt_cosh (a * τ / c)).comp τ
    (hasDerivAt_arg a c τ)).const_mul (c ^ 2 / a))
  convert h using 1
  field_simp

/-- Second proper-time derivative of the Minkowski time: `d²t/dτ² = (a/c) sinh (a τ / c)`. -/
theorem hasDerivAt_rindlerTime_deriv (a c τ : ℝ) :
    HasDerivAt (fun s : ℝ => Real.cosh (a * s / c)) ((a / c) * Real.sinh (a * τ / c)) τ := by
  have h := (Real.hasDerivAt_cosh (a * τ / c)).comp τ (hasDerivAt_arg a c τ)
  convert h using 1
  ring

/-- Second proper-time derivative of the Minkowski position: `d²x/dτ² = a cosh (a τ / c)`. -/
theorem hasDerivAt_rindlerPos_deriv (ha : a ≠ 0) (hc : c ≠ 0) (τ : ℝ) :
    HasDerivAt (fun s : ℝ => c * Real.sinh (a * s / c)) (a * Real.cosh (a * τ / c)) τ := by
  have h := ((Real.hasDerivAt_sinh (a * τ / c)).comp τ (hasDerivAt_arg a c τ)).const_mul c
  convert h using 1
  field_simp

/-- The Rindler worldline is parametrised by proper time: its four-velocity has Minkowski
square `c² (dt/dτ)² − (dx/dτ)² = c²`. -/
theorem rindler_fourVelocity_normalized (ha : a ≠ 0) (hc : c ≠ 0) (τ : ℝ) :
    c ^ 2 * (deriv (rindlerTime a c) τ) ^ 2 - (deriv (rindlerPos a c) τ) ^ 2 = c ^ 2 := by
  rw [(hasDerivAt_rindlerTime ha hc τ).deriv, (hasDerivAt_rindlerPos ha hc τ).deriv]
  have := Real.cosh_sq_sub_sinh_sq (a * τ / c)
  nlinarith [this]

/-- The Rindler worldline has constant proper acceleration of magnitude `a`:
`(d²x/dτ²)² − c² (d²t/dτ²)² = a²`. -/
theorem rindler_properAcceleration (ha : a ≠ 0) (hc : c ≠ 0) (τ : ℝ) :
    (deriv (fun s : ℝ => c * Real.sinh (a * s / c)) τ) ^ 2
      - c ^ 2 * (deriv (fun s : ℝ => Real.cosh (a * s / c)) τ) ^ 2 = a ^ 2 := by
  rw [(hasDerivAt_rindlerPos_deriv ha hc τ).deriv, (hasDerivAt_rindlerTime_deriv a c τ).deriv]
  have h := Real.cosh_sq_sub_sinh_sq (a * τ / c)
  have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc
  field_simp
  nlinarith [h]

/-!
## Periodicity in imaginary proper time

Analytically continuing the Rindler worldline to complex proper time, it is periodic with
period `2 π i c / a`.  This imaginary-time periodicity is exactly the KMS condition at
inverse temperature `β = 2 π c / (ħ a)` in units where the Boltzmann factor is
`exp (-β ħ ω)`, and it is what forces the detected temperature to be the Unruh temperature.
-/

/-- Complexified Minkowski time of the Rindler observer. -/
noncomputable def rindlerTimeC (a c : ℝ) (z : ℂ) : ℂ := ((c : ℂ) / a) * Complex.sinh (a * z / c)

/-- Complexified Minkowski position of the Rindler observer. -/
noncomputable def rindlerPosC (a c : ℝ) (z : ℂ) : ℂ :=
  ((c : ℂ) ^ 2 / a) * Complex.cosh (a * z / c)

/-- The imaginary period of the analytically continued Rindler worldline, `2 π c / a`. -/
noncomputable def rindlerImaginaryPeriod (a c : ℝ) : ℝ := 2 * Real.pi * c / a

private lemma arg_shift (ha : a ≠ 0) (hc : c ≠ 0) (z : ℂ) :
    (a : ℂ) * (z + Complex.I * (rindlerImaginaryPeriod a c : ℝ)) / c
      = (a : ℂ) * z / c + 2 * Real.pi * Complex.I := by
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  simp only [rindlerImaginaryPeriod, Complex.ofReal_div, Complex.ofReal_mul,
    Complex.ofReal_ofNat]
  field_simp

/-- **Imaginary-time periodicity of the Rindler worldline.**  Continued to complex proper
time, the uniformly accelerated trajectory is periodic with imaginary period `2 π c / a`;
this is the KMS periodicity responsible for the thermal character of the Unruh effect. -/
theorem rindler_imaginary_time_periodic (ha : a ≠ 0) (hc : c ≠ 0) (z : ℂ) :
    rindlerTimeC a c (z + Complex.I * (rindlerImaginaryPeriod a c : ℝ)) = rindlerTimeC a c z ∧
    rindlerPosC a c (z + Complex.I * (rindlerImaginaryPeriod a c : ℝ)) = rindlerPosC a c z := by
  constructor <;>
    simp [rindlerTimeC, rindlerPosC, arg_shift ha hc z, Complex.sinh, Complex.cosh,
      Complex.exp_add, Complex.exp_two_pi_mul_I, Complex.exp_neg]

/-!
## The Unruh temperature
-/

/-- The Unruh (Davies–Unruh) temperature `T = ℏ a / (2 π c k_B)` seen by an observer
undergoing uniform proper acceleration `a`, where `ℏ` is the reduced Planck constant,
`c` the speed of light and `k_B` Boltzmann's constant. -/
noncomputable def unruhTemperature (hbar a c kB : ℝ) : ℝ :=
  hbar * a / (2 * Real.pi * c * kB)

/-- **Unruh effect.**  For positive `ℏ`, proper acceleration `a`, speed of light `c` and
Boltzmann constant `k_B`, the Unruh temperature `T = ℏ a / (2 π c k_B)`:

* is positive, and satisfies `k_B T = ℏ a / (2 π c)`;
* reproduces, for every energy `E`, the Boltzmann factor `exp (-2 π c E / (ℏ a))` and the
  Bose–Einstein occupation `(exp (2 π c E / (ℏ a)) - 1)⁻¹` seen by the accelerated observer
  in the Minkowski vacuum;
* is the unique positive temperature doing so;
* is the unique positive temperature whose thermal (KMS) period `β ℏ = ℏ / (k_B T)` equals
  the imaginary proper-time period `2 π c / a` of the Rindler worldline
  (`rindler_imaginary_time_periodic`).
-/
theorem unruh_effect (hbar a c kB : ℝ) (hhbar : 0 < hbar) (ha : 0 < a) (hc : 0 < c)
    (hkB : 0 < kB) :
    0 < unruhTemperature hbar a c kB ∧
    kB * unruhTemperature hbar a c kB = hbar * a / (2 * Real.pi * c) ∧
    (∀ E : ℝ, Real.exp (-(E / (kB * unruhTemperature hbar a c kB)))
        = Real.exp (-(2 * Real.pi * c * E / (hbar * a)))) ∧
    (∀ E : ℝ, (Real.exp (E / (kB * unruhTemperature hbar a c kB)) - 1)⁻¹
        = (Real.exp (2 * Real.pi * c * E / (hbar * a)) - 1)⁻¹) ∧
    (∀ T : ℝ, 0 < T →
      (∀ E : ℝ, Real.exp (-(E / (kB * T))) = Real.exp (-(2 * Real.pi * c * E / (hbar * a)))) →
      T = unruhTemperature hbar a c kB) ∧
    (∀ T : ℝ, 0 < T →
      (hbar / (kB * T) = rindlerImaginaryPeriod a c ↔ T = unruhTemperature hbar a c kB)) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hden : (0 : ℝ) < 2 * Real.pi * c * kB := by positivity
  have hT : 0 < unruhTemperature hbar a c kB := by
    unfold unruhTemperature
    positivity
  have hkT : kB * unruhTemperature hbar a c kB = hbar * a / (2 * Real.pi * c) := by
    unfold unruhTemperature
    field_simp
  refine ⟨hT, hkT, ?_, ?_, ?_, ?_⟩
  · intro E
    rw [hkT]
    congr 1
    field_simp
  · intro E
    rw [hkT]
    congr 3
    field_simp
  · intro T hTpos hEq
    have h1 := hEq 1
    have h2 : 1 / (kB * T) = 2 * Real.pi * c * 1 / (hbar * a) := by
      have := Real.exp_injective h1
      linarith
    have hkT' : 0 < kB * T := by positivity
    have hha : 0 < hbar * a := by positivity
    unfold unruhTemperature
    field_simp at h2 ⊢
    nlinarith [h2]
  · intro T hTpos
    have hkT' : 0 < kB * T := by positivity
    unfold rindlerImaginaryPeriod unruhTemperature
    rw [div_eq_div_iff (by positivity) (by positivity)]
    constructor
    · intro h
      field_simp
      nlinarith [h]
    · intro h
      subst h
      field_simp

/-- **Thermal spectrum from the Bogoliubov coefficients.**  In the Rindler quantisation of
a massless field, the Bogoliubov coefficients relating Minkowski and Rindler modes of
angular frequency `ω` satisfy the normalisation `|α|² - |β|² = 1` together with the
relation `|β|² = |α|² exp (-2 π c ω / a)` coming from the analytic structure of the modes
(equivalently, from the imaginary proper-time periodicity
`rindler_imaginary_time_periodic`).  These two relations already force the mean particle
number `|β|²` detected by the accelerated observer to be the Bose–Einstein occupation at
the Unruh temperature. -/
theorem unruh_particle_number (hbar a c kB omega A B : ℝ) (hhbar : 0 < hbar) (ha : 0 < a)
    (hc : 0 < c) (hkB : 0 < kB) (homega : 0 < omega) (hnorm : A - B = 1)
    (hratio : B = A * Real.exp (-(2 * Real.pi * c * omega / a))) :
    B = (Real.exp (hbar * omega / (kB * unruhTemperature hbar a c kB)) - 1)⁻¹ := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hxpos : 0 < 2 * Real.pi * c * omega / a := by positivity
  set x : ℝ := 2 * Real.pi * c * omega / a with hxdef
  have hqpos : 0 < Real.exp (-x) := Real.exp_pos _
  have hqlt : Real.exp (-x) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hone : (1 : ℝ) - Real.exp (-x) ≠ 0 := by linarith
  have hA : A * (1 - Real.exp (-x)) = 1 := by
    rw [hratio] at hnorm
    linear_combination hnorm
  have hB : B = Real.exp (-x) / (1 - Real.exp (-x)) := by
    rw [hratio]
    field_simp
    linear_combination hA
  have hexp : hbar * omega / (kB * unruhTemperature hbar a c kB) = x := by
    unfold unruhTemperature
    rw [hxdef]
    field_simp
  have hinv : Real.exp x = (Real.exp (-x))⁻¹ := by
    rw [Real.exp_neg, inv_inv]
  rw [hexp, hinv, hB]
  field_simp

end Phys

