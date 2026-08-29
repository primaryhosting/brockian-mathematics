import Mathlib
/-!
# Unruh Effect
Category: Frontier Phys
Target: Phys.unruh_effect
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
The Unruh effect: an observer moving with constant proper acceleration `a` through the
Minkowski vacuum of a massless scalar field perceives a thermal bath at the temperature

                            T = ℏ a / (2 π c k_B).

The formalisation below is organised as follows.

* `Phys.rindlerTime`, `Phys.rindlerPos` : the uniformly accelerated (Rindler) worldline,
  parametrised by proper time `τ`.
* `Phys.properAccelSq` : the Minkowski square of the four-acceleration; it is shown to be
  identically `a ^ 2`, i.e. the worldline really has constant proper acceleration `a`.
* `Phys.intervalSq` : the invariant interval between two points of the worldline; it is shown
  to equal `(2 c ^ 2 / a) ^ 2 * sinh (a (τ - τ') / (2 c)) ^ 2`.
* `Phys.wightman` : the vacuum two-point (Wightman) function of a massless scalar field
  restricted to the accelerated worldline and continued to complex proper time; it is shown to
  be the standard `-ℏ / (4 π ^ 2 s ^ 2)` expression in terms of the invariant interval.
* `Phys.unruhTemperature` : the Unruh temperature `ℏ a / (2 π c k_B)`.
* The KMS (Kubo–Martin–Schwinger) property: the Wightman function is periodic in imaginary
  proper time with period `ℏ / (k_B T)` exactly when `T` is the Unruh temperature.  Periodicity
  in imaginary time with period `ℏ / (k_B T)` is precisely the statement that the state looks
  thermal at temperature `T`.
* `Phys.bose` : the Bose–Einstein occupation number, satisfying detailed balance at the Unruh
  temperature, `n / (n + 1) = exp (-2 π c E / (ℏ a))`.

The main theorem `Phys.unruh_effect` collects these statements.
-/

namespace Phys

open Real

/-- Time coordinate of the uniformly accelerated (Rindler) worldline, as a function of the
proper time `τ`. -/
noncomputable def rindlerTime (c a τ : ℝ) : ℝ := (c / a) * Real.sinh (a * τ / c)

/-- Space coordinate of the uniformly accelerated (Rindler) worldline, as a function of the
proper time `τ`. -/
noncomputable def rindlerPos (c a τ : ℝ) : ℝ := (c ^ 2 / a) * Real.cosh (a * τ / c)

/-- The Minkowski square of the four-acceleration of the Rindler worldline. -/
noncomputable def properAccelSq (c a τ : ℝ) : ℝ :=
  (deriv (deriv (rindlerPos c a)) τ) ^ 2 - (deriv (deriv (fun s => c * rindlerTime c a s)) τ) ^ 2

/-- The invariant (Minkowski) interval squared between two points of the worldline,
`s² = c²Δt² - Δx²`. -/
noncomputable def intervalSq (c a τ τ' : ℝ) : ℝ :=
  c ^ 2 * (rindlerTime c a τ - rindlerTime c a τ') ^ 2
    - (rindlerPos c a τ - rindlerPos c a τ') ^ 2

/-- The Unruh temperature `T = ℏ a / (2 π c k_B)`. -/
noncomputable def unruhTemperature (hbar c a kB : ℝ) : ℝ := hbar * a / (2 * π * c * kB)

/-- The vacuum Wightman two-point function of a massless scalar field, restricted to the
uniformly accelerated worldline and analytically continued to complex proper time `z`.  (The
`iε`-prescription of the Wightman function is implemented by the analytic continuation.) -/
noncomputable def wightman (hbar c a : ℝ) (z : ℂ) : ℂ :=
  -((hbar : ℂ) / (16 * (π : ℂ) ^ 2)) * ((a : ℂ) / (c : ℂ) ^ 2) ^ 2
    / Complex.sinh ((a : ℂ) * z / (2 * (c : ℂ))) ^ 2

/-- The Bose–Einstein occupation number of a mode of energy `E` at temperature `T`. -/
noncomputable def bose (E T kB : ℝ) : ℝ := 1 / (Real.exp (E / (kB * T)) - 1)

/-! ### Derivatives of the Rindler worldline -/

private theorem hasDerivAt_lin (a c τ : ℝ) : HasDerivAt (fun s : ℝ => a * s / c) (a / c) τ := by
  simpa [mul_comm, mul_div_assoc] using ((hasDerivAt_id τ).const_mul a).div_const c

theorem deriv_rindlerTime (c a : ℝ) (hc : c ≠ 0) (ha : a ≠ 0) :
    deriv (rindlerTime c a) = fun τ => Real.cosh (a * τ / c) := by
  funext τ
  have h : HasDerivAt (rindlerTime c a) ((c / a) * (Real.cosh (a * τ / c) * (a / c))) τ :=
    ((Real.hasDerivAt_sinh _).comp τ (hasDerivAt_lin a c τ)).const_mul _
  rw [h.deriv]; field_simp

theorem deriv_rindlerPos (c a : ℝ) (hc : c ≠ 0) (ha : a ≠ 0) :
    deriv (rindlerPos c a) = fun τ => c * Real.sinh (a * τ / c) := by
  funext τ
  have h : HasDerivAt (rindlerPos c a) ((c ^ 2 / a) * (Real.sinh (a * τ / c) * (a / c))) τ :=
    ((Real.hasDerivAt_cosh _).comp τ (hasDerivAt_lin a c τ)).const_mul _
  rw [h.deriv]; field_simp

theorem deriv2_rindlerPos (c a : ℝ) (hc : c ≠ 0) (ha : a ≠ 0) :
    deriv (deriv (rindlerPos c a)) = fun τ => a * Real.cosh (a * τ / c) := by
  rw [deriv_rindlerPos c a hc ha]
  funext τ
  have h : HasDerivAt (fun s : ℝ => c * Real.sinh (a * s / c))
      (c * (Real.cosh (a * τ / c) * (a / c))) τ :=
    ((Real.hasDerivAt_sinh _).comp τ (hasDerivAt_lin a c τ)).const_mul _
  rw [h.deriv]; field_simp

theorem deriv2_rindlerTime (c a : ℝ) (hc : c ≠ 0) (ha : a ≠ 0) :
    deriv (deriv (fun s => c * rindlerTime c a s)) = fun τ => c * (a / c) * Real.sinh (a * τ / c) := by
  have h1 : deriv (fun s => c * rindlerTime c a s) = fun τ => c * Real.cosh (a * τ / c) := by
    funext τ
    have h : HasDerivAt (fun s : ℝ => c * rindlerTime c a s)
        (c * ((c / a) * (Real.cosh (a * τ / c) * (a / c)))) τ :=
      (((Real.hasDerivAt_sinh _).comp τ (hasDerivAt_lin a c τ)).const_mul _).const_mul _
    rw [h.deriv]; field_simp
  rw [h1]
  funext τ
  have h : HasDerivAt (fun s : ℝ => c * Real.cosh (a * s / c))
      (c * (Real.sinh (a * τ / c) * (a / c))) τ :=
    ((Real.hasDerivAt_cosh _).comp τ (hasDerivAt_lin a c τ)).const_mul _
  rw [h.deriv]; ring

/-! ### The worldline has constant proper acceleration `a` -/

/-- The four-velocity of the Rindler worldline is normalised, `u · u = c²`; equivalently, `τ`
really is the proper time along the worldline. -/
theorem fourVelocity_norm (c a : ℝ) (hc : c ≠ 0) (ha : a ≠ 0) (τ : ℝ) :
    (c * deriv (rindlerTime c a) τ) ^ 2 - (deriv (rindlerPos c a) τ) ^ 2 = c ^ 2 := by
  have h := Real.cosh_sq_sub_sinh_sq (a * τ / c)
  rw [deriv_rindlerTime c a hc ha, deriv_rindlerPos c a hc ha]
  nlinarith [h]

/-- The Rindler worldline is uniformly accelerated: the Minkowski norm of its four-acceleration
is the constant `a`. -/
theorem properAccelSq_eq (c a : ℝ) (hc : c ≠ 0) (ha : a ≠ 0) (τ : ℝ) :
    properAccelSq c a τ = a ^ 2 := by
  have h := Real.cosh_sq_sub_sinh_sq (a * τ / c)
  simp only [properAccelSq, deriv2_rindlerPos c a hc ha, deriv2_rindlerTime c a hc ha]
  field_simp
  nlinarith [h]

/-! ### The invariant interval along the worldline -/

private theorem sinh_cosh_diff_sq (s d : ℝ) :
    (Real.sinh (s + d) - Real.sinh (s - d)) ^ 2 - (Real.cosh (s + d) - Real.cosh (s - d)) ^ 2
      = 4 * Real.sinh d ^ 2 := by
  simp only [Real.sinh_add, Real.sinh_sub, Real.cosh_add, Real.cosh_sub]
  nlinarith [Real.cosh_sq_sub_sinh_sq s, Real.cosh_sq_sub_sinh_sq d]

/-- The invariant interval between two points of the uniformly accelerated worldline. -/
theorem intervalSq_eq (c a : ℝ) (hc : c ≠ 0) (ha : a ≠ 0) (τ τ' : ℝ) :
    intervalSq c a τ τ' = (2 * c ^ 2 / a) ^ 2 * Real.sinh (a * (τ - τ') / (2 * c)) ^ 2 := by
  set s : ℝ := (a * τ / c + a * τ' / c) / 2 with hs
  set d : ℝ := a * (τ - τ') / (2 * c) with hd
  have h1 : a * τ / c = s + d := by rw [hs, hd]; field_simp; ring
  have h2 : a * τ' / c = s - d := by rw [hs, hd]; field_simp; ring
  have key := sinh_cosh_diff_sq s d
  simp only [intervalSq, rindlerTime, rindlerPos, h1, h2]
  field_simp
  nlinarith [key]

/-! ### The Wightman function along the worldline -/

/-- Along the uniformly accelerated worldline the massless Wightman function takes the standard
form `-ℏ / (4 π² s²)`, where `s²` is the invariant interval. -/
theorem wightman_eq_of_real (hbar c a : ℝ) (hc : c ≠ 0) (ha : a ≠ 0) (τ : ℝ) :
    wightman hbar c a (τ : ℂ) = ((-(hbar / (4 * π ^ 2)) / intervalSq c a τ 0 : ℝ) : ℂ) := by
  have hI := intervalSq_eq c a hc ha τ 0
  have hτ : a * (τ - 0) / (2 * c) = a * τ / (2 * c) := by ring_nf
  rw [hτ] at hI
  have hsinh : Complex.sinh ((a : ℂ) * (τ : ℂ) / (2 * (c : ℂ)))
      = ((Real.sinh (a * τ / (2 * c)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sinh]
    push_cast
    ring_nf
  rw [wightman, hsinh, hI]
  by_cases h0 : Real.sinh (a * τ / (2 * c)) = 0
  · rw [h0]
    simp
  · have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
    have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha
    have h0' : ((Real.sinh (a * τ / (2 * c)) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h0
    have hpi : (π : ℝ) ≠ 0 := Real.pi_ne_zero
    have hpi' : ((π : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpi
    push_cast
    field_simp
    ring

/-! ### KMS condition: thermality at the Unruh temperature -/

private theorem complex_sinh_sub_pi_I (w : ℂ) : Complex.sinh (w - (π : ℂ) * Complex.I)
    = -Complex.sinh w := by
  rw [Complex.sinh_sub]
  simp [Complex.cosh_mul_I, Complex.sinh_mul_I]

/-- The imaginary-time period predicted by the KMS condition, `ℏ / (k_B T)`, evaluated at the
Unruh temperature, equals `2 π c / a`. -/
theorem kms_period (hbar c a kB : ℝ) (hhbar : hbar ≠ 0) (hkB : kB ≠ 0) :
    hbar / (kB * unruhTemperature hbar c a kB) = 2 * π * c / a := by
  rw [unruhTemperature]
  by_cases ha : a = 0
  · simp [ha]
  · field_simp

/-- **KMS condition.**  The Wightman function on the uniformly accelerated worldline is periodic
in imaginary proper time with period `ℏ / (k_B T)` where `T` is the Unruh temperature: this is
exactly the statement that the accelerated observer sees a thermal state at temperature `T`. -/
theorem wightman_kms (hbar c a kB : ℝ) (hc : c ≠ 0) (ha : a ≠ 0) (hhbar : hbar ≠ 0)
    (hkB : kB ≠ 0) (z : ℂ) :
    wightman hbar c a (z - Complex.I * ((hbar / (kB * unruhTemperature hbar c a kB) : ℝ) : ℂ))
      = wightman hbar c a z := by
  rw [kms_period hbar c a kB hhbar hkB]
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  have harg : (a : ℂ) * (z - Complex.I * ((2 * π * c / a : ℝ) : ℂ)) / (2 * (c : ℂ))
      = (a : ℂ) * z / (2 * (c : ℂ)) - (π : ℂ) * Complex.I := by
    push_cast
    field_simp
  rw [wightman, wightman, harg, complex_sinh_sub_pi_I]
  ring

/-! ### Detailed balance / Planck factor -/

private theorem bose_ratio (x : ℝ) (hx : 0 < x) :
    1 / (Real.exp x - 1) / (1 / (Real.exp x - 1) + 1) = Real.exp (-x) := by
  have hexp : 1 < Real.exp x := by simpa using Real.exp_lt_exp.mpr hx
  have hne : Real.exp x - 1 ≠ 0 := by linarith
  rw [Real.exp_neg]
  field_simp
  ring

/-- The dimensionless ratio `E / (k_B T)` at the Unruh temperature is `2 π c E / (ℏ a)`. -/
theorem unruh_exponent (hbar c a kB E : ℝ) (hc : 0 < c) (ha : 0 < a) (hhbar : 0 < hbar)
    (hkB : 0 < kB) :
    E / (kB * unruhTemperature hbar c a kB) = 2 * π * c * E / (hbar * a) := by
  have h1 : hbar * a ≠ 0 := by positivity
  have h2 : (2 : ℝ) * π * c ≠ 0 := by positivity
  rw [unruhTemperature]
  field_simp

/-- **Detailed balance.**  At the Unruh temperature the Bose–Einstein occupation numbers obey
`n / (n + 1) = exp (-E / (k_B T)) = exp (-2 π c E / (ℏ a))`, the hallmark of a thermal
(Planckian) spectrum at temperature `T = ℏ a / (2 π c k_B)`. -/
theorem bose_detailed_balance (hbar c a kB E : ℝ) (hc : 0 < c) (ha : 0 < a) (hhbar : 0 < hbar)
    (hkB : 0 < kB) (hE : 0 < E) :
    bose E (unruhTemperature hbar c a kB) kB / (bose E (unruhTemperature hbar c a kB) kB + 1)
      = Real.exp (-(E / (kB * unruhTemperature hbar c a kB)))
    ∧ bose E (unruhTemperature hbar c a kB) kB / (bose E (unruhTemperature hbar c a kB) kB + 1)
      = Real.exp (-(2 * π * c * E) / (hbar * a)) := by
  have hxe := unruh_exponent hbar c a kB E hc ha hhbar hkB
  have hxpos : 0 < E / (kB * unruhTemperature hbar c a kB) := by
    rw [hxe]
    have h1 : 0 < hbar * a := by positivity
    have h2 : 0 < 2 * π * c * E := by positivity
    exact div_pos h2 h1
  have hb : bose E (unruhTemperature hbar c a kB) kB
      = 1 / (Real.exp (E / (kB * unruhTemperature hbar c a kB)) - 1) := rfl
  have hmain := bose_ratio _ hxpos
  rw [hb]
  refine ⟨hmain, ?_⟩
  rw [hmain, hxe]
  congr 1
  ring

/-! ### Main theorem -/

/-- **The Unruh effect.**

For an observer with constant proper acceleration `a` moving through the Minkowski vacuum of a
massless scalar field:

0. the four-velocity of the worldline is normalised (`τ` is the proper time);
1. the Rindler worldline `τ ↦ ((c/a) sinh (aτ/c), (c²/a) cosh (aτ/c))` has constant proper
   acceleration `a`;
2. the invariant interval between two of its points is `(2c²/a)² sinh²(a(τ-τ')/(2c))`;
3. the vacuum Wightman function restricted to the worldline is the standard massless
   two-point function `-ℏ/(4π² s²)` of that interval;
4. that Wightman function is periodic in imaginary proper time with period `ℏ / (k_B T)`
   (the KMS condition, i.e. thermality at temperature `T`) for
   `T = T_U := ℏ a / (2 π c k_B)`, the period being `2 π c / a`;
5. the corresponding occupation numbers obey Planckian detailed balance
   `n/(n+1) = exp(-E/(k_B T_U)) = exp(-2π c E/(ℏ a))`;
6. and the temperature so identified is `T_U = ℏ a / (2 π c k_B)`, the **Unruh temperature**.
-/
theorem unruh_effect (hbar c a kB : ℝ) (hc : 0 < c) (ha : 0 < a) (hhbar : 0 < hbar)
    (hkB : 0 < kB) :
    (∀ τ : ℝ, (c * deriv (rindlerTime c a) τ) ^ 2 - (deriv (rindlerPos c a) τ) ^ 2 = c ^ 2) ∧
    (∀ τ : ℝ, properAccelSq c a τ = a ^ 2) ∧
    (∀ τ τ' : ℝ, intervalSq c a τ τ'
        = (2 * c ^ 2 / a) ^ 2 * Real.sinh (a * (τ - τ') / (2 * c)) ^ 2) ∧
    (∀ τ : ℝ, wightman hbar c a (τ : ℂ)
        = ((-(hbar / (4 * π ^ 2)) / intervalSq c a τ 0 : ℝ) : ℂ)) ∧
    (hbar / (kB * unruhTemperature hbar c a kB) = 2 * π * c / a) ∧
    (∀ z : ℂ, wightman hbar c a
        (z - Complex.I * ((hbar / (kB * unruhTemperature hbar c a kB) : ℝ) : ℂ))
        = wightman hbar c a z) ∧
    (∀ E : ℝ, 0 < E →
      bose E (unruhTemperature hbar c a kB) kB / (bose E (unruhTemperature hbar c a kB) kB + 1)
        = Real.exp (-(E / (kB * unruhTemperature hbar c a kB)))) ∧
    unruhTemperature hbar c a kB = hbar * a / (2 * π * c * kB) := by
  have hc' : c ≠ 0 := ne_of_gt hc
  have ha' : a ≠ 0 := ne_of_gt ha
  refine ⟨fun τ => fourVelocity_norm c a hc' ha' τ, fun τ => properAccelSq_eq c a hc' ha' τ, fun τ τ' => intervalSq_eq c a hc' ha' τ τ',
    fun τ => wightman_eq_of_real hbar c a hc' ha' τ,
    kms_period hbar c a kB (ne_of_gt hhbar) (ne_of_gt hkB),
    fun z => wightman_kms hbar c a kB hc' ha' (ne_of_gt hhbar) (ne_of_gt hkB) z, ?_, rfl⟩
  intro E hE
  exact (bose_detailed_balance hbar c a kB E hc ha hhbar hkB hE).1

end Phys

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

