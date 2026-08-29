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

noncomputable def rindlerInverseTemperature (hbar a c : ℝ) : ℝ := 2 * π * c / (hbar * a)

/-- The Unruh temperature is positive for positive acceleration. -/
