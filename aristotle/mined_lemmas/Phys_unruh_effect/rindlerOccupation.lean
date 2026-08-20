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

noncomputable def rindlerOccupation (a c ω : ℝ) : ℝ :=
  1 / (Real.exp (2 * Real.pi * c * ω / a) - 1)

/-- **Unruh effect.**  A uniformly accelerated observer with proper acceleration `a > 0`
sees the Minkowski vacuum as a thermal bath.  The temperature of that bath is

  `T = ℏ a / (2 π c k_B)`,

which is: (1) positive; (2) the temperature whose Boltzmann factor `exp (-ℏω/(k_B T))`
reproduces, for every mode frequency `ω`, the Rindler thermality factor
`exp (-2 π c ω / a)` obtained from the Bogoliubov coefficients; (3) the *unique* positive
temperature with that property; and (4) the temperature whose Planck spectrum coincides
with the spectrum registered by the accelerated detector. -/
