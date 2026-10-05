/-
# Unruh Effect
Category: Frontier Phys
Target: Phys.unruh_effect
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Unruh Effect
Category: Frontier Phys
Target: Phys.unruh_effect
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

A uniformly accelerated observer in the Minkowski vacuum perceives a thermal bath at the
Unruh temperature `T = ℏ a / (2 π c k_B)`.

The file develops the statement in three layers.

1. *Kinematics of the Rindler worldline.*  The hyperbolic worldline
   `x⁰(τ) = (c²/a) sinh (a τ / c)`, `x¹(τ) = (c²/a) cosh (a τ / c)` is parametrised by proper
   time and has constant proper acceleration of magnitude `a`
   (`Phys.rindler_fourVelocity_normalized`, `Phys.rindler_properAcceleration`).
2. *Thermality from imaginary-time periodicity.*  The Minkowski interval between two points of
   this worldline depends only on the proper-time difference, and its analytic continuation
   `Phys.rindlerIntervalC` is periodic in imaginary proper time with period `2 π c / a`
   (`Phys.rindler_interval_eq`, `Phys.rindlerIntervalC_periodic`).  This is the KMS condition,
   whose period is `ℏ / (k_B T)`; equating the two periods yields the Unruh temperature.
3. *The Unruh temperature itself* (`Phys.unruhTemperature`) together with the detailed-balance
   relation, its uniqueness, and the resulting Planck spectrum (`Phys.unruh_effect`).
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

namespace Phys

/-! ## The Unruh temperature and the Planck spectrum -/

/-- The **Unruh temperature** `T = ℏ a / (2 π c k_B)` associated with a uniformly
accelerated observer of proper acceleration `a`, where `ℏ` is the reduced Planck
constant, `c` the speed of light and `k_B` Boltzmann's constant. -/
noncomputable def unruhTemperature (hbar c kB a : ℝ) : ℝ :=
  hbar * a / (2 * Real.pi * c * kB)

/-- The Planck (Bose–Einstein) occupation number at temperature `T` for a mode of
angular frequency `ω`: `n(ω) = 1 / (exp (ℏ ω / (k_B T)) - 1)`. -/
noncomputable def planckOccupation (hbar kB T ω : ℝ) : ℝ :=
  1 / (Real.exp (hbar * ω / (kB * T)) - 1)

/-- Positivity of the Unruh temperature for positive acceleration. -/
theorem unruhTemperature_pos {hbar c kB a : ℝ} (hhbar : 0 < hbar) (hc : 0 < c)
    (hkB : 0 < kB) (ha : 0 < a) : 0 < unruhTemperature hbar c kB a := by
  unfold unruhTemperature
  positivity

/-! ## Kinematics of the uniformly accelerated (Rindler) worldline -/

/-- Time component `x⁰(τ) = (c²/a) sinh (a τ / c)` of the uniformly accelerated worldline,
parametrised by proper time `τ`. -/
noncomputable def rindlerTime (c a τ : ℝ) : ℝ := (c ^ 2 / a) * Real.sinh (a * τ / c)

/-- Space component `x¹(τ) = (c²/a) cosh (a τ / c)` of the uniformly accelerated worldline,
parametrised by proper time `τ`. -/
noncomputable def rindlerSpace (c a τ : ℝ) : ℝ := (c ^ 2 / a) * Real.cosh (a * τ / c)

/-- The time component of the four-velocity: `dx⁰/dτ = c cosh (a τ / c)`. -/
theorem hasDerivAt_rindlerTime (c a τ : ℝ) (hc : c ≠ 0) (ha : a ≠ 0) :
    HasDerivAt (rindlerTime c a) (c * Real.cosh (a * τ / c)) τ := by
  have h1 : HasDerivAt (fun t : ℝ => a * t / c) (a / c) τ := by
    simpa using ((hasDerivAt_id τ).const_mul a).div_const c
  have h2 := (Real.hasDerivAt_sinh (a * τ / c)).comp τ h1
  have h3 := h2.const_mul (c ^ 2 / a)
  convert h3 using 1
  field_simp

/-- The space component of the four-velocity: `dx¹/dτ = c sinh (a τ / c)`. -/
theorem hasDerivAt_rindlerSpace (c a τ : ℝ) (hc : c ≠ 0) (ha : a ≠ 0) :
    HasDerivAt (rindlerSpace c a) (c * Real.sinh (a * τ / c)) τ := by
  have h1 : HasDerivAt (fun t : ℝ => a * t / c) (a / c) τ := by
    simpa using ((hasDerivAt_id τ).const_mul a).div_const c
  have h2 := (Real.hasDerivAt_cosh (a * τ / c)).comp τ h1
  have h3 := h2.const_mul (c ^ 2 / a)
  convert h3 using 1
  field_simp

/-- The time component of the four-acceleration: `d²x⁰/dτ² = a sinh (a τ / c)`. -/
theorem hasDerivAt_rindlerVelocityTime (c a τ : ℝ) (hc : c ≠ 0) :
    HasDerivAt (fun t : ℝ => c * Real.cosh (a * t / c)) (a * Real.sinh (a * τ / c)) τ := by
  have h1 : HasDerivAt (fun t : ℝ => a * t / c) (a / c) τ := by
    simpa using ((hasDerivAt_id τ).const_mul a).div_const c
  have h2 := (Real.hasDerivAt_cosh (a * τ / c)).comp τ h1
  have h3 := h2.const_mul c
  convert h3 using 1
  field_simp

/-- The space component of the four-acceleration: `d²x¹/dτ² = a cosh (a τ / c)`. -/
theorem hasDerivAt_rindlerVelocitySpace (c a τ : ℝ) (hc : c ≠ 0) :
    HasDerivAt (fun t : ℝ => c * Real.sinh (a * t / c)) (a * Real.cosh (a * τ / c)) τ := by
  have h1 : HasDerivAt (fun t : ℝ => a * t / c) (a / c) τ := by
    simpa using ((hasDerivAt_id τ).const_mul a).div_const c
  have h2 := (Real.hasDerivAt_sinh (a * τ / c)).comp τ h1
  have h3 := h2.const_mul c
  convert h3 using 1
  field_simp

/-- The worldline is parametrised by proper time: the four-velocity `u = (dx⁰/dτ, dx¹/dτ)`
satisfies `(u⁰)² - (u¹)² = c²`. -/
theorem rindler_fourVelocity_normalized (c a τ : ℝ) :
    (c * Real.cosh (a * τ / c)) ^ 2 - (c * Real.sinh (a * τ / c)) ^ 2 = c ^ 2 := by
  have h := Real.cosh_sq_sub_sinh_sq (a * τ / c)
  nlinarith [h]

/-- The worldline has constant proper acceleration of magnitude `a`: the four-acceleration
`A = (d²x⁰/dτ², d²x¹/dτ²)` is spacelike with `(A¹)² - (A⁰)² = a²`. -/
theorem rindler_properAcceleration (c a τ : ℝ) :
    (a * Real.cosh (a * τ / c)) ^ 2 - (a * Real.sinh (a * τ / c)) ^ 2 = a ^ 2 := by
  have h := Real.cosh_sq_sub_sinh_sq (a * τ / c)
  nlinarith [h]

/-! ## Imaginary-time periodicity (KMS condition) -/

/-- The analytic continuation to complex proper-time separation `z` of the Minkowski interval
between two points of the uniformly accelerated worldline:
`Δs²(z) = -(4 c⁴ / a²) sinh² (a z / (2 c))`. -/
noncomputable def rindlerIntervalC (c a : ℝ) (z : ℂ) : ℂ :=
  -(4 * (c : ℂ) ^ 4 / (a : ℂ) ^ 2) * (Complex.sinh ((a : ℂ) * z / (2 * (c : ℂ)))) ^ 2

/-- The Minkowski interval between the worldline points at proper times `τ₁` and `τ₂` depends
only on `τ₁ - τ₂` and equals `-(4 c⁴/a²) sinh² (a (τ₁ - τ₂) / (2 c))`. -/
theorem rindler_interval_eq (c a t1 t2 : ℝ) (hc : c ≠ 0) (ha : a ≠ 0) :
    (rindlerSpace c a t1 - rindlerSpace c a t2) ^ 2
        - (rindlerTime c a t1 - rindlerTime c a t2) ^ 2
      = -(4 * c ^ 4 / a ^ 2) * (Real.sinh (a * (t1 - t2) / (2 * c))) ^ 2 := by
  unfold rindlerSpace rindlerTime
  set u1 := a * t1 / c with hu1
  set u2 := a * t2 / c with hu2
  have hy : a * (t1 - t2) / (2 * c) = (u1 - u2) / 2 := by rw [hu1, hu2]; field_simp
  have hcs : Real.cosh (u1 - u2) = 2 * Real.sinh ((u1 - u2) / 2) ^ 2 + 1 := by
    have h2 := Real.cosh_two_mul ((u1 - u2) / 2)
    have hs := Real.sinh_sq ((u1 - u2) / 2)
    have h3 : 2 * ((u1 - u2) / 2) = u1 - u2 := by ring
    rw [h3] at h2
    linarith
  have hsub := Real.cosh_sub u1 u2
  have e1 := Real.cosh_sq_sub_sinh_sq u1
  have e2 := Real.cosh_sq_sub_sinh_sq u2
  rw [hy]
  linear_combination (c ^ 2 / a) ^ 2 * e1 + (c ^ 2 / a) ^ 2 * e2 + 2 * (c ^ 2 / a) ^ 2 * hsub
    - 2 * (c ^ 2 / a) ^ 2 * hcs

/-- On real proper-time separations the complexified interval agrees with the Minkowski
interval along the worldline. -/
theorem rindlerIntervalC_ofReal (c a t1 t2 : ℝ) (hc : c ≠ 0) (ha : a ≠ 0) :
    rindlerIntervalC c a ((t1 - t2 : ℝ) : ℂ)
      = ((rindlerSpace c a t1 - rindlerSpace c a t2) ^ 2
          - (rindlerTime c a t1 - rindlerTime c a t2) ^ 2 : ℝ) := by
  rw [rindler_interval_eq c a t1 t2 hc ha]
  unfold rindlerIntervalC
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  have harg : (a : ℂ) * ((t1 - t2 : ℝ) : ℂ) / (2 * (c : ℂ))
      = ((a * (t1 - t2) / (2 * c) : ℝ) : ℂ) := by push_cast; ring
  rw [harg, ← Complex.ofReal_sinh]
  push_cast
  ring

/-- **KMS periodicity.**  The complexified interval along the uniformly accelerated worldline
is periodic in imaginary proper time with period `2 π c / a`.  This periodicity of the vacuum
correlation function restricted to the worldline is exactly the KMS condition at inverse
temperature `β` with `ℏ β = 2 π c / a`. -/
theorem rindlerIntervalC_periodic (c a : ℝ) (hc : c ≠ 0) (ha : a ≠ 0) (z : ℂ) :
    rindlerIntervalC c a (z + Complex.I * ((2 * Real.pi * c / a : ℝ) : ℂ))
      = rindlerIntervalC c a z := by
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  unfold rindlerIntervalC
  have harg : (a : ℂ) * (z + Complex.I * ((2 * Real.pi * c / a : ℝ) : ℂ)) / (2 * (c : ℂ))
      = (a : ℂ) * z / (2 * (c : ℂ)) + (Real.pi : ℂ) * Complex.I := by
    push_cast
    field_simp
  rw [harg, Complex.sinh_add, Complex.cosh_mul_I, Complex.sinh_mul_I, Complex.cos_pi,
    Complex.sin_pi]
  ring

/-! ## The Unruh effect -/

/--
**The Unruh effect.**

For a uniformly accelerated observer with proper acceleration `a > 0`, the Minkowski vacuum
appears as a thermal bath at the Unruh temperature `T = ℏ a / (2 π c k_B)`.

The statement packages the characteristic properties of this temperature:

* `T` is positive and equals `ℏ a / (2 π c k_B)`;
* **KMS condition from the worldline geometry**: the analytically continued interval along the
  accelerated worldline is periodic in imaginary proper time with period `ℏ / (k_B T)`, i.e.
  `ℏ β`, which is precisely the thermality criterion at temperature `T`;
* **detailed balance**: the Boltzmann weight `exp (-E / (k_B T))` at temperature `T` coincides,
  for every energy `E`, with the Rindler weight `exp (-2 π c E / (ℏ a))` dictated by that
  periodicity (equivalently, the Bogoliubov ratio `|β_ω|² / |α_ω|² = exp (-2 π c ω / a)`);
* `T` is the *unique* positive temperature satisfying the detailed-balance relation;
* **Planck spectrum**: the response of the accelerated detector,
  `1 / (exp (2 π c ω / a) - 1)`, is exactly the Planck occupation number at temperature `T`;
* the temperature is proportional to the acceleration: `T (λ a) = λ * T (a)`.
-/
theorem unruh_effect (hbar c kB a : ℝ) (hhbar : 0 < hbar) (hc : 0 < c) (hkB : 0 < kB)
    (ha : 0 < a) :
    ∃ T : ℝ, 0 < T ∧ T = hbar * a / (2 * Real.pi * c * kB) ∧
      T = unruhTemperature hbar c kB a ∧
      (∀ z : ℂ, rindlerIntervalC c a (z + Complex.I * ((hbar / (kB * T) : ℝ) : ℂ))
        = rindlerIntervalC c a z) ∧
      (∀ E : ℝ, Real.exp (-(E / (kB * T))) = Real.exp (-(2 * Real.pi * c * E / (hbar * a)))) ∧
      (∀ T' : ℝ, 0 < T' →
        (∀ E : ℝ, Real.exp (-(E / (kB * T'))) =
          Real.exp (-(2 * Real.pi * c * E / (hbar * a)))) → T' = T) ∧
      (∀ ω : ℝ, 0 < ω →
        1 / (Real.exp (2 * Real.pi * c * ω / a) - 1) = planckOccupation hbar kB T ω) ∧
      (∀ lam : ℝ, unruhTemperature hbar c kB (lam * a) = lam * T) := by
  set T : ℝ := unruhTemperature hbar c kB a with hT
  have hTpos : 0 < T := unruhTemperature_pos hhbar hc hkB ha
  have hTval : T = hbar * a / (2 * Real.pi * c * kB) := rfl
  -- the key scaling identity: `k_B * T = ℏ a / (2 π c)`
  have hkT : kB * T = hbar * a / (2 * Real.pi * c) := by
    rw [hTval]; field_simp
  -- exponent identity
  have hexp : ∀ E : ℝ, E / (kB * T) = 2 * Real.pi * c * E / (hbar * a) := by
    intro E
    rw [hkT]
    field_simp
  refine ⟨T, hTpos, hTval, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · -- the KMS period `ℏ / (k_B T)` is the imaginary-time period `2 π c / a`
    intro z
    have hperiod : hbar / (kB * T) = 2 * Real.pi * c / a := by
      rw [hkT]
      field_simp
    rw [hperiod]
    exact rindlerIntervalC_periodic c a (ne_of_gt hc) (ne_of_gt ha) z
  · intro E; rw [hexp E]
  · intro T' hT' h
    have h1 := h 1
    have hinj : (1 : ℝ) / (kB * T') = 2 * Real.pi * c * 1 / (hbar * a) := by
      have := Real.exp_eq_exp.mp h1
      linarith
    have hkk : kB * T' = kB * T := by
      rw [hkT]
      field_simp at hinj ⊢
      linarith [hinj]
    exact mul_left_cancel₀ (ne_of_gt hkB) hkk
  · intro ω _
    unfold planckOccupation
    have hw : hbar * ω / (kB * T) = 2 * Real.pi * c * ω / a := by
      rw [hkT]
      field_simp
    rw [hw]
  · intro lam
    unfold unruhTemperature
    rw [hT]
    unfold unruhTemperature
    field_simp

end Phys

