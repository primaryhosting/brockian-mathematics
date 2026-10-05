/-
/-!
# Unruh Effect
Category: Frontier Phys
Target: Phys.unruh_effect
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/

import Mathlib

/-!
# Unruh Effect
Category: Frontier Phys
Target: Phys.unruh_effect
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open scoped Real

set_option maxHeartbeats 1000000

namespace Phys

/-! ## The Unruh temperature -/

/-- The Unruh temperature `T = ℏ a / (2 π c k_B)` seen by an observer with proper
acceleration `a`. -/
noncomputable def unruhTemperature (hbar a c kB : ℝ) : ℝ :=
  hbar * a / (2 * Real.pi * c * kB)

/-- Planck (Bose–Einstein) occupation number of a mode of angular frequency `ω`
at temperature `T`. -/
noncomputable def planckOccupation (hbar kB T ω : ℝ) : ℝ :=
  1 / (Real.exp (hbar * ω / (kB * T)) - 1)

/-! ## The uniformly accelerated (Rindler) worldline -/

/-- Space coordinate of the worldline of a uniformly accelerated observer,
parametrised by proper time `τ`. -/
noncomputable def rindlerX (a c τ : ℝ) : ℝ := (c ^ 2 / a) * Real.cosh (a * τ / c)

/-- Time coordinate of the worldline of a uniformly accelerated observer,
parametrised by proper time `τ`. -/
noncomputable def rindlerT (a c τ : ℝ) : ℝ := (c / a) * Real.sinh (a * τ / c)

/-- Space coordinate of the Euclidean continuation of the Rindler worldline. -/
noncomputable def rindlerXE (a c τ : ℝ) : ℝ := (c ^ 2 / a) * Real.cos (a * τ / c)

/-- Time coordinate of the Euclidean continuation of the Rindler worldline. -/
noncomputable def rindlerTE (a c τ : ℝ) : ℝ := (c / a) * Real.sin (a * τ / c)

/-! ### Kinematics -/

theorem rindler_hyperbola (a c τ : ℝ) :
    (rindlerX a c τ) ^ 2 - c ^ 2 * (rindlerT a c τ) ^ 2 = (c ^ 2 / a) ^ 2 := by
  have h := Real.cosh_sq_sub_sinh_sq (a * τ / c)
  unfold rindlerX rindlerT
  linear_combination ((c ^ 2 / a) ^ 2) * h

theorem hasDerivAt_rindlerX (a c τ : ℝ) (ha : a ≠ 0) (hc : c ≠ 0) :
    HasDerivAt (rindlerX a c) (c * Real.sinh (a * τ / c)) τ := by
  have h0 : HasDerivAt (fun τ : ℝ => a * τ / c) (a / c) τ := by
    simpa [mul_comm, mul_div_assoc] using
      ((hasDerivAt_id τ).const_mul a).div_const c
  have h1 : HasDerivAt (fun τ : ℝ => Real.cosh (a * τ / c))
      (Real.sinh (a * τ / c) * (a / c)) τ := h0.cosh
  have h2 := h1.const_mul (c ^ 2 / a)
  convert h2 using 1
  field_simp

theorem hasDerivAt_rindlerT (a c τ : ℝ) (ha : a ≠ 0) (hc : c ≠ 0) :
    HasDerivAt (rindlerT a c) (Real.cosh (a * τ / c)) τ := by
  have h0 : HasDerivAt (fun τ : ℝ => a * τ / c) (a / c) τ := by
    simpa [mul_comm, mul_div_assoc] using
      ((hasDerivAt_id τ).const_mul a).div_const c
  have h1 : HasDerivAt (fun τ : ℝ => Real.sinh (a * τ / c))
      (Real.cosh (a * τ / c) * (a / c)) τ := h0.sinh
  have h2 := h1.const_mul (c / a)
  convert h2 using 1
  field_simp

/-- The parameter `τ` is indeed proper time: the four-velocity is normalised,
`c² (dt/dτ)² - (dx/dτ)² = c²`. -/
theorem rindler_four_velocity_norm (a c τ : ℝ) (ha : a ≠ 0) (hc : c ≠ 0) :
    c ^ 2 * (deriv (rindlerT a c) τ) ^ 2 - (deriv (rindlerX a c) τ) ^ 2 = c ^ 2 := by
  rw [(hasDerivAt_rindlerT a c τ ha hc).deriv, (hasDerivAt_rindlerX a c τ ha hc).deriv]
  have h := Real.cosh_sq_sub_sinh_sq (a * τ / c)
  nlinarith [h]

/-- The worldline has constant proper acceleration `a`: the four-acceleration is a
spacelike vector of norm `a`, `(d²x/dτ²)² - c² (d²t/dτ²)² = a²`. -/
theorem rindler_proper_acceleration (a c : ℝ) (ha : a ≠ 0) (hc : c ≠ 0) (τ : ℝ) :
    (deriv (deriv (rindlerX a c)) τ) ^ 2 - c ^ 2 * (deriv (deriv (rindlerT a c)) τ) ^ 2
      = a ^ 2 := by
  have hX : deriv (rindlerX a c) = fun τ => c * Real.sinh (a * τ / c) := by
    funext s; exact (hasDerivAt_rindlerX a c s ha hc).deriv
  have hT : deriv (rindlerT a c) = fun τ => Real.cosh (a * τ / c) := by
    funext s; exact (hasDerivAt_rindlerT a c s ha hc).deriv
  have h0 : HasDerivAt (fun τ : ℝ => a * τ / c) (a / c) τ := by
    simpa [mul_comm, mul_div_assoc] using
      ((hasDerivAt_id τ).const_mul a).div_const c
  have hX2 : deriv (deriv (rindlerX a c)) τ = a * Real.cosh (a * τ / c) := by
    rw [hX]
    have : HasDerivAt (fun τ : ℝ => c * Real.sinh (a * τ / c))
        (c * (Real.cosh (a * τ / c) * (a / c))) τ := (h0.sinh).const_mul c
    rw [this.deriv]; field_simp
  have hT2 : deriv (deriv (rindlerT a c)) τ = (a / c) * Real.sinh (a * τ / c) := by
    rw [hT]
    have : HasDerivAt (fun τ : ℝ => Real.cosh (a * τ / c))
        (Real.sinh (a * τ / c) * (a / c)) τ := h0.cosh
    rw [this.deriv]; ring
  rw [hX2, hT2]
  have h := Real.cosh_sq_sub_sinh_sq (a * τ / c)
  field_simp
  nlinarith [h]

/-! ### Euclidean periodicity: the KMS condition -/

/-- Under continuation to imaginary time the worldline becomes a circle, periodic in
Euclidean proper time with period `β = 2 π c / a`. -/
theorem rindler_euclidean_periodic (a c : ℝ) (ha : a ≠ 0) (hc : c ≠ 0) (τ : ℝ) :
    rindlerXE a c (τ + 2 * Real.pi * c / a) = rindlerXE a c τ ∧
    rindlerTE a c (τ + 2 * Real.pi * c / a) = rindlerTE a c τ := by
  have harg : a * (τ + 2 * Real.pi * c / a) / c = a * τ / c + 2 * Real.pi := by
    field_simp
  constructor
  · simp [rindlerXE, harg, Real.cos_add_two_pi]
  · simp [rindlerTE, harg, Real.sin_add_two_pi]

/-- The Euclidean period `β = 2 π c / a` is exactly the inverse temperature
`ℏ / (k_B T)` for the Unruh temperature `T`. -/
theorem unruh_kms (hbar a c kB : ℝ) (hhbar : hbar ≠ 0) (ha : a ≠ 0) (hc : c ≠ 0)
    (hkB : kB ≠ 0) :
    hbar / (kB * unruhTemperature hbar a c kB) = 2 * Real.pi * c / a := by
  unfold unruhTemperature
  field_simp

theorem unruhTemperature_pos (hbar a c kB : ℝ) (hhbar : 0 < hbar) (ha : 0 < a) (hc : 0 < c)
    (hkB : 0 < kB) : 0 < unruhTemperature hbar a c kB := by
  unfold unruhTemperature
  positivity

/-- The Unruh temperature is the unique temperature whose inverse temperature matches the
Euclidean (KMS) period `2 π c / a` of the accelerated observer. -/
theorem unruhTemperature_unique (hbar a c kB : ℝ) (hhbar : 0 < hbar) (ha : 0 < a) (hc : 0 < c)
    (hkB : 0 < kB) (T : ℝ) (hT : 0 < T) :
    hbar / (kB * T) = 2 * Real.pi * c / a ↔ T = unruhTemperature hbar a c kB := by
  have hpi := Real.pi_pos
  constructor
  · intro h
    unfold unruhTemperature
    field_simp at h ⊢
    linarith [h]
  · rintro rfl
    exact unruh_kms hbar a c kB hhbar.ne' ha.ne' hc.ne' hkB.ne'

/-- The response of the accelerated detector, governed by the Rindler factor
`1 / (exp (2 π c ω / a) - 1)`, is exactly a Planck spectrum at the Unruh temperature. -/
theorem unruh_planck_spectrum (hbar a c kB : ℝ) (hhbar : 0 < hbar) (ha : 0 < a) (hc : 0 < c)
    (hkB : 0 < kB) (ω : ℝ) :
    planckOccupation hbar kB (unruhTemperature hbar a c kB) ω
      = 1 / (Real.exp (2 * Real.pi * c * ω / a) - 1) := by
  unfold planckOccupation
  have hkms := unruh_kms hbar a c kB hhbar.ne' ha.ne' hc.ne' hkB.ne'
  have : hbar * ω / (kB * unruhTemperature hbar a c kB) = 2 * Real.pi * c * ω / a := by
    rw [mul_comm hbar ω, mul_div_assoc, hkms]; ring
  rw [this]

/-! ## The Unruh effect -/

/--
**The Unruh effect.**

An observer moving with constant proper acceleration `a` (hypotheses: `ℏ, a, c, k_B > 0`)
perceives the Minkowski vacuum as a thermal bath at the *Unruh temperature*

  `T = ℏ a / (2 π c k_B)`.

The statement packages the standard derivation:

1. the hyperbolic worldline `x = (c²/a) cosh(aτ/c)`, `t = (c/a) sinh(aτ/c)` is parametrised
   by proper time (`c² (dt/dτ)² - (dx/dτ)² = c²`) and has constant proper acceleration `a`;
2. its Euclidean continuation is periodic in imaginary proper time with period
   `β = 2 π c / a`;
3. this KMS period corresponds to the inverse temperature `ℏ / (k_B T)` for, and only for,
   `T = ℏ a / (2 π c k_B) = unruhTemperature ℏ a c k_B`, which is positive;
4. consequently the detector response `1 / (exp (2 π c ω / a) - 1)` is exactly a Planck
   spectrum at that temperature.
-/
theorem unruh_effect (hbar a c kB : ℝ) (hhbar : 0 < hbar) (ha : 0 < a) (hc : 0 < c)
    (hkB : 0 < kB) :
    -- (0) the Unruh temperature
    unruhTemperature hbar a c kB = hbar * a / (2 * Real.pi * c * kB) ∧
    0 < unruhTemperature hbar a c kB ∧
    -- (1) uniformly accelerated worldline, parametrised by proper time
    (∀ τ : ℝ, c ^ 2 * (deriv (rindlerT a c) τ) ^ 2 - (deriv (rindlerX a c) τ) ^ 2 = c ^ 2) ∧
    (∀ τ : ℝ, (deriv (deriv (rindlerX a c)) τ) ^ 2
        - c ^ 2 * (deriv (deriv (rindlerT a c)) τ) ^ 2 = a ^ 2) ∧
    -- (2) Euclidean periodicity with period β = 2π c / a
    (∀ τ : ℝ, rindlerXE a c (τ + 2 * Real.pi * c / a) = rindlerXE a c τ ∧
        rindlerTE a c (τ + 2 * Real.pi * c / a) = rindlerTE a c τ) ∧
    -- (3) the KMS period fixes the temperature uniquely
    (∀ T : ℝ, 0 < T → (hbar / (kB * T) = 2 * Real.pi * c / a ↔
        T = unruhTemperature hbar a c kB)) ∧
    -- (4) thermal (Planck) spectrum at the Unruh temperature
    (∀ ω : ℝ, planckOccupation hbar kB (unruhTemperature hbar a c kB) ω
        = 1 / (Real.exp (2 * Real.pi * c * ω / a) - 1)) := by
  refine ⟨rfl, unruhTemperature_pos hbar a c kB hhbar ha hc hkB,
    fun τ => rindler_four_velocity_norm a c τ ha.ne' hc.ne',
    fun τ => rindler_proper_acceleration a c ha.ne' hc.ne' τ,
    fun τ => rindler_euclidean_periodic a c ha.ne' hc.ne' τ,
    fun T hT => unruhTemperature_unique hbar a c kB hhbar ha hc hkB T hT,
    fun ω => unruh_planck_spectrum hbar a c kB hhbar ha hc hkB ω⟩

end Phys

