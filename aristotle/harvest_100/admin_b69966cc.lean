/-
# Unruh Effect
Category: Frontier Phys
Target: Phys.unruh_effect
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 requires `import` to come before any module docstring, so the required header
-- above is an ordinary block comment.)

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

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Phys

/-! ## The uniformly accelerated (Rindler) worldline

In `(1+1)`-dimensional Minkowski space with metric `-c² dt² + dx²`, the worldline of an
observer with constant proper acceleration `a`, parameterised by proper time `τ`, is

`t(τ) = (c/a) sinh (a τ / c)`,  `x(τ) = (c²/a) cosh (a τ / c)`.
-/

/-- Minkowski time coordinate of the uniformly accelerated observer, as a function of
proper time. -/
noncomputable def rindlerTime (a c τ : ℝ) : ℝ := (c / a) * Real.sinh (a * τ / c)

/-- Minkowski space coordinate of the uniformly accelerated observer, as a function of
proper time. -/
noncomputable def rindlerPos (a c τ : ℝ) : ℝ := (c ^ 2 / a) * Real.cosh (a * τ / c)

/-- Time component of the four-velocity. -/
noncomputable def rindlerVelTime (a c τ : ℝ) : ℝ := Real.cosh (a * τ / c)

/-- Space component of the four-velocity. -/
noncomputable def rindlerVelPos (a c τ : ℝ) : ℝ := c * Real.sinh (a * τ / c)

/-- Time component of the four-acceleration. -/
noncomputable def rindlerAccTime (a c τ : ℝ) : ℝ := (a / c) * Real.sinh (a * τ / c)

/-- Space component of the four-acceleration. -/
noncomputable def rindlerAccPos (a c τ : ℝ) : ℝ := a * Real.cosh (a * τ / c)

section Worldline

variable {a c : ℝ}

private lemma hasDerivAt_arg (τ : ℝ) :
    HasDerivAt (fun s : ℝ => a * s / c) (a / c) τ := by
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
    ((hasDerivAt_id τ).const_mul a).div_const c

lemma hasDerivAt_rindlerTime (ha : a ≠ 0) (hc : c ≠ 0) (τ : ℝ) :
    HasDerivAt (rindlerTime a c) (rindlerVelTime a c τ) τ := by
  have key : rindlerVelTime a c τ = c / a * (Real.cosh (a * τ / c) * (a / c)) := by
    simp only [rindlerVelTime]
    field_simp
  rw [key]
  exact ((Real.hasDerivAt_sinh (a * τ / c)).comp τ (hasDerivAt_arg τ)).const_mul (c / a)

lemma hasDerivAt_rindlerPos (ha : a ≠ 0) (hc : c ≠ 0) (τ : ℝ) :
    HasDerivAt (rindlerPos a c) (rindlerVelPos a c τ) τ := by
  have key : rindlerVelPos a c τ = c ^ 2 / a * (Real.sinh (a * τ / c) * (a / c)) := by
    simp only [rindlerVelPos]
    field_simp
  rw [key]
  exact ((Real.hasDerivAt_cosh (a * τ / c)).comp τ (hasDerivAt_arg τ)).const_mul (c ^ 2 / a)

lemma hasDerivAt_rindlerVelTime (τ : ℝ) :
    HasDerivAt (rindlerVelTime a c) (rindlerAccTime a c τ) τ := by
  have key : rindlerAccTime a c τ = Real.sinh (a * τ / c) * (a / c) := by
    simp only [rindlerAccTime]; ring
  rw [key]
  exact (Real.hasDerivAt_cosh (a * τ / c)).comp τ (hasDerivAt_arg τ)

lemma hasDerivAt_rindlerVelPos (ha : a ≠ 0) (hc : c ≠ 0) (τ : ℝ) :
    HasDerivAt (rindlerVelPos a c) (rindlerAccPos a c τ) τ := by
  have key : rindlerAccPos a c τ = c * (Real.cosh (a * τ / c) * (a / c)) := by
    simp only [rindlerAccPos]
    field_simp
  rw [key]
  exact ((Real.hasDerivAt_sinh (a * τ / c)).comp τ (hasDerivAt_arg τ)).const_mul c

lemma deriv_rindlerTime (ha : a ≠ 0) (hc : c ≠ 0) :
    deriv (rindlerTime a c) = rindlerVelTime a c :=
  funext fun τ => (hasDerivAt_rindlerTime ha hc τ).deriv

lemma deriv_rindlerPos (ha : a ≠ 0) (hc : c ≠ 0) :
    deriv (rindlerPos a c) = rindlerVelPos a c :=
  funext fun τ => (hasDerivAt_rindlerPos ha hc τ).deriv

lemma deriv2_rindlerTime (ha : a ≠ 0) (hc : c ≠ 0) :
    deriv (deriv (rindlerTime a c)) = rindlerAccTime a c := by
  rw [deriv_rindlerTime ha hc]
  exact funext fun τ => (hasDerivAt_rindlerVelTime τ).deriv

lemma deriv2_rindlerPos (ha : a ≠ 0) (hc : c ≠ 0) :
    deriv (deriv (rindlerPos a c)) = rindlerAccPos a c := by
  rw [deriv_rindlerPos ha hc]
  exact funext fun τ => (hasDerivAt_rindlerVelPos ha hc τ).deriv

/-- The worldline is parameterised by proper time: the four-velocity has Minkowski
square `-c²`. -/
lemma rindler_unit_velocity (ha : a ≠ 0) (hc : c ≠ 0) (τ : ℝ) :
    -c ^ 2 * (deriv (rindlerTime a c) τ) ^ 2 + (deriv (rindlerPos a c) τ) ^ 2 = -c ^ 2 := by
  rw [deriv_rindlerTime ha hc, deriv_rindlerPos ha hc]
  have h := Real.cosh_sq_sub_sinh_sq (a * τ / c)
  simp only [rindlerVelTime, rindlerVelPos]
  nlinarith [h, sq_nonneg c]

/-- The worldline has constant proper acceleration `a`: the four-acceleration has
Minkowski square `a²`. -/
lemma rindler_proper_acceleration (ha : a ≠ 0) (hc : c ≠ 0) (τ : ℝ) :
    -c ^ 2 * (deriv (deriv (rindlerTime a c)) τ) ^ 2
      + (deriv (deriv (rindlerPos a c)) τ) ^ 2 = a ^ 2 := by
  rw [deriv2_rindlerTime ha hc, deriv2_rindlerPos ha hc]
  have h := Real.cosh_sq_sub_sinh_sq (a * τ / c)
  simp only [rindlerAccTime, rindlerAccPos]
  field_simp
  nlinarith [h]

end Worldline

/-! ## The Unruh temperature -/

/-- The Unruh temperature `T = ℏ a / (2 π c k_B)` seen by an observer with proper
acceleration `a`. -/
noncomputable def unruhTemperature (hbar a c kB : ℝ) : ℝ :=
  hbar * a / (2 * Real.pi * c * kB)

lemma unruhTemperature_pos {hbar a c kB : ℝ} (hh : 0 < hbar) (ha : 0 < a) (hc : 0 < c)
    (hk : 0 < kB) : 0 < unruhTemperature hbar a c kB := by
  have : (0:ℝ) < 2 * Real.pi * c * kB := by positivity
  exact div_pos (by positivity) this

/-- **KMS condition.** A thermal state at temperature `T` has Euclidean (imaginary-time)
period `ℏ / (k_B T)`; the Rindler observer's Wightman function is periodic in imaginary
proper time with period `2 π c / a`. The unique positive temperature matching these two
periods is the Unruh temperature. -/
lemma unruh_kms_unique {hbar a c kB : ℝ} (hh : 0 < hbar) (ha : 0 < a) (hc : 0 < c)
    (hk : 0 < kB) {T : ℝ} (hT : 0 < T) :
    hbar / (kB * T) = 2 * Real.pi * c / a ↔ T = unruhTemperature hbar a c kB := by
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have h1 : (kB * T) ≠ 0 := by positivity
  have h2 : a ≠ 0 := ne_of_gt ha
  have h3 : (2 * Real.pi * c * kB) ≠ 0 := by positivity
  rw [unruhTemperature]
  constructor
  · intro h
    field_simp at h ⊢
    nlinarith [h]
  · intro h
    subst h
    field_simp

/-- **Detailed balance.** The Rindler thermal factor `exp (-2 π c ω / a)` of the Unruh
radiation is exactly the Boltzmann factor `exp (-ℏ ω / (k_B T))` at the Unruh
temperature. -/
lemma unruh_boltzmann_factor {hbar a c kB : ℝ} (hh : 0 < hbar) (ha : 0 < a) (hc : 0 < c)
    (hk : 0 < kB) (ω : ℝ) :
    Real.exp (-(hbar * ω) / (kB * unruhTemperature hbar a c kB))
      = Real.exp (-(2 * Real.pi * c * ω) / a) := by
  congr 1
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  rw [unruhTemperature]
  field_simp

/-- **Planck spectrum.** The mean occupation number of a mode of frequency `ω` seen by the
accelerated detector is the Bose–Einstein distribution at the Unruh temperature. -/
lemma unruh_bose_einstein {hbar a c kB : ℝ} (hh : 0 < hbar) (ha : 0 < a) (hc : 0 < c)
    (hk : 0 < kB) (ω : ℝ) :
    1 / (Real.exp (hbar * ω / (kB * unruhTemperature hbar a c kB)) - 1)
      = 1 / (Real.exp (2 * Real.pi * c * ω / a) - 1) := by
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have : hbar * ω / (kB * unruhTemperature hbar a c kB) = 2 * Real.pi * c * ω / a := by
    rw [unruhTemperature]
    field_simp
  rw [this]

/-! ## Main theorem -/

/-- **The Unruh effect.**  An observer moving with constant proper acceleration `a`
through the Minkowski vacuum perceives a thermal bath at the Unruh temperature

`T = ℏ a / (2 π c k_B)`.

The statement collects:

1. the worldline `t(τ) = (c/a) sinh(aτ/c)`, `x(τ) = (c²/a) cosh(aτ/c)` is parameterised by
   proper time (four-velocity of Minkowski square `-c²`) and has constant proper
   acceleration `a` (four-acceleration of Minkowski square `a²`);
2. the Unruh temperature is positive;
3. it is the *unique* positive temperature whose thermal (KMS) imaginary-time period
   `ℏ/(k_B T)` equals the `2π c / a` periodicity of the Rindler propagator in imaginary
   proper time;
4. the corresponding Boltzmann factor and Bose–Einstein occupation numbers coincide with
   the Rindler ones;
5. the explicit formula `T = ℏ a / (2 π c k_B)`.
-/
theorem unruh_effect {hbar a c kB : ℝ} (hh : 0 < hbar) (ha : 0 < a) (hc : 0 < c)
    (hk : 0 < kB) :
    (∀ τ : ℝ, -c ^ 2 * (deriv (rindlerTime a c) τ) ^ 2
        + (deriv (rindlerPos a c) τ) ^ 2 = -c ^ 2) ∧
    (∀ τ : ℝ, -c ^ 2 * (deriv (deriv (rindlerTime a c)) τ) ^ 2
        + (deriv (deriv (rindlerPos a c)) τ) ^ 2 = a ^ 2) ∧
    0 < unruhTemperature hbar a c kB ∧
    (∀ T : ℝ, 0 < T →
      (hbar / (kB * T) = 2 * Real.pi * c / a ↔ T = unruhTemperature hbar a c kB)) ∧
    (∀ ω : ℝ, Real.exp (-(hbar * ω) / (kB * unruhTemperature hbar a c kB))
        = Real.exp (-(2 * Real.pi * c * ω) / a)) ∧
    (∀ ω : ℝ, 1 / (Real.exp (hbar * ω / (kB * unruhTemperature hbar a c kB)) - 1)
        = 1 / (Real.exp (2 * Real.pi * c * ω / a) - 1)) ∧
    unruhTemperature hbar a c kB = hbar * a / (2 * Real.pi * c * kB) := by
  refine ⟨fun τ => rindler_unit_velocity ha.ne' hc.ne' τ,
    fun τ => rindler_proper_acceleration ha.ne' hc.ne' τ,
    unruhTemperature_pos hh ha hc hk,
    fun T hT => unruh_kms_unique hh ha hc hk hT,
    fun ω => unruh_boltzmann_factor hh ha hc hk ω,
    fun ω => unruh_bose_einstein hh ha hc hk ω, rfl⟩

end Phys

