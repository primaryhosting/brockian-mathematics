/-
# Bekenstein Bound
Category: Frontier Phys
Target: Phys.bekenstein_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Phys

/-- The Bekenstein limit `2 π k R E / (ℏ c)`: the universal upper bound on the
thermodynamic entropy of a system of energy `E` contained in a sphere of radius `R`. -/

noncomputable def blackHoleEntropyOfEnergy (k G E hbar c : ℝ) : ℝ :=
  4 * Real.pi * k * G * E ^ 2 / (hbar * c ^ 5)

/-- Consistency check: the Bekenstein–Hawking formula `S = k c ^ 3 A / (4 G ℏ)` applied to a
Schwarzschild horizon of radius `R = 2 G E / c ^ 4` and area `A = 4 π R ^ 2` indeed gives
`blackHoleEntropyOfEnergy`. -/
