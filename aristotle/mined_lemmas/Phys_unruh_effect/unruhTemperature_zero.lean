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
