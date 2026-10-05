/-
# Unruh Effect
Category: Frontier Phys
Target: Phys.unruh_effect
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Phys

open Real

/-- The Unruh temperature `T = ℏ a / (2 π c k)` seen by an observer with proper
acceleration `a`, where `ℏ` is the reduced Planck constant, `c` the speed of light
and `k` Boltzmann's constant. -/
noncomputable def unruhTemperature (hbar a c k : ℝ) : ℝ := hbar * a / (2 * π * c * k)

/-- The inverse temperature (in energy units) `β = 2 π c / (ℏ a)` obtained from the
periodicity `2 π c / a` of the Rindler observer's proper time in imaginary time
(the KMS/Euclidean-periodicity condition). -/
noncomputable def rindlerInverseTemperature (hbar a c : ℝ) : ℝ := 2 * π * c / (hbar * a)

/-- The Unruh temperature is positive for positive acceleration. -/
theorem unruhTemperature_pos {hbar a c k : ℝ} (hhbar : 0 < hbar) (ha : 0 < a)
    (hc : 0 < c) (hk : 0 < k) : 0 < unruhTemperature hbar a c k := by
  have : 0 < 2 * π * c * k := by positivity
  exact div_pos (by positivity) this

/-- The Unruh temperature is strictly increasing in the proper acceleration. -/
theorem unruhTemperature_strictMono {hbar c k : ℝ} (hhbar : 0 < hbar) (hc : 0 < c)
    (hk : 0 < k) {a₁ a₂ : ℝ} (h : a₁ < a₂) :
    unruhTemperature hbar a₁ c k < unruhTemperature hbar a₂ c k := by
  have hden : 0 < 2 * π * c * k := by positivity
  unfold unruhTemperature
  apply div_lt_div_of_pos_right _ hden
  nlinarith

/-- A vanishing acceleration means zero Unruh temperature: an inertial observer sees
the vacuum as a zero-temperature state. -/
theorem unruhTemperature_zero (hbar c k : ℝ) : unruhTemperature hbar 0 c k = 0 := by
  simp [unruhTemperature]

/-- **Unruh effect.**  For an observer with proper acceleration `a > 0`, the Euclidean
(KMS) periodicity condition `1 / (k T) = 2 π c / (ℏ a)` — i.e. the inverse temperature
in energy units equals the Rindler imaginary-time period `2 π c / (ℏ a)` — determines
the temperature uniquely, and it is the Unruh temperature

  `T = ℏ a / (2 π c k)`.

Conversely this temperature does satisfy the KMS condition, and the corresponding
detailed-balance (Boltzmann) factor for a mode of frequency `ω` is
`exp (-ℏ ω / (k T)) = exp (-2 π c ω / a)`. -/
theorem unruh_effect {hbar a c k : ℝ} (hhbar : 0 < hbar) (ha : 0 < a) (hc : 0 < c)
    (hk : 0 < k) :
    (∀ T : ℝ, 0 < T →
        (1 / (k * T) = rindlerInverseTemperature hbar a c ↔
          T = unruhTemperature hbar a c k)) ∧
      0 < unruhTemperature hbar a c k ∧
      1 / (k * unruhTemperature hbar a c k) = rindlerInverseTemperature hbar a c ∧
      ∀ ω : ℝ, Real.exp (-(hbar * ω) / (k * unruhTemperature hbar a c k))
          = Real.exp (-(2 * π * c * ω) / a) := by
  have hpi : (0:ℝ) < π := Real.pi_pos
  have hden : (0:ℝ) < 2 * π * c * k := by positivity
  have hTU : unruhTemperature hbar a c k = hbar * a / (2 * π * c * k) := rfl
  have hUpos : 0 < unruhTemperature hbar a c k := unruhTemperature_pos hhbar ha hc hk
  have hkey : 1 / (k * unruhTemperature hbar a c k) = rindlerInverseTemperature hbar a c := by
    rw [hTU]
    unfold rindlerInverseTemperature
    field_simp
  refine ⟨?_, hUpos, hkey, ?_⟩
  · intro T hT
    constructor
    · intro h
      have hkT : k * T ≠ 0 := by positivity
      have hR : rindlerInverseTemperature hbar a c = 2 * π * c / (hbar * a) := rfl
      rw [hR] at h
      have hha : (0:ℝ) < hbar * a := by positivity
      field_simp at h
      rw [hTU]
      field_simp
      nlinarith [h]
    · intro h; rw [h]; exact hkey
  · intro ω
    congr 1
    rw [hTU]
    field_simp

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

