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

theorem unruhTemperature_strictMono {hbar c k : ℝ} (hhbar : 0 < hbar) (hc : 0 < c)
    (hk : 0 < k) {a₁ a₂ : ℝ} (h : a₁ < a₂) :
    unruhTemperature hbar a₁ c k < unruhTemperature hbar a₂ c k := by
  have hden : 0 < 2 * π * c * k := by positivity
  unfold unruhTemperature
  apply div_lt_div_of_pos_right _ hden
  nlinarith

/-- A vanishing acceleration means zero Unruh temperature: an inertial observer sees
the vacuum as a zero-temperature state. -/
