/-
# Unruh Effect
Category: Frontier Phys
Target: Phys.unruh_effect
Statement: State the Unruh temperature T = ℏa/(2πck) seen by a uniformly accelerated observer.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Phys

open Real

/-- The Unruh temperature `T = ℏ a / (2 π c k_B)` seen by an observer with proper
acceleration `a`, expressed in terms of the reduced Planck constant `hbar`, the speed of
light `c` and Boltzmann's constant `kB`. -/

noncomputable def unruhTemperature (hbar a c kB : ℝ) : ℝ :=
  hbar * a / (2 * Real.pi * c * kB)

/-- The Planck (Bose–Einstein) occupation number at temperature `T` for a mode of
angular frequency `ω`. -/
