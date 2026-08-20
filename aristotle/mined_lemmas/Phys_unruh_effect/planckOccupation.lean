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

noncomputable def planckOccupation (hbar kB T ω : ℝ) : ℝ :=
  1 / (Real.exp (hbar * ω / (kB * T)) - 1)

/-- The occupation number of the Rindler (uniformly accelerated) detector for a mode of
angular frequency `ω`: the Bogoliubov transformation between Minkowski and Rindler modes
produces the factor `exp (2 π c ω / a)` in the denominator. -/
