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

noncomputable def bekensteinLimit (k R E hbar c : ℝ) : ℝ :=
  2 * Real.pi * k * R * E / (hbar * c)

/-- The Bekenstein–Hawking entropy of a Schwarzschild black hole of energy `E`
(horizon area `A = 4 π (2 G E / c ^ 4) ^ 2`, entropy `S = k c ^ 3 A / (4 G ℏ)`),
expressed in terms of the energy: `4 π k G E ^ 2 / (ℏ c ^ 5)`. -/
