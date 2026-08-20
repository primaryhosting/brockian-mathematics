import Mathlib

/-!
# Bekenstein Bound
Category: Frontier Phys
Target: Phys.bekenstein_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

open Real

/-- The Bekenstein–Hawking entropy `S = k c³ A / (4 G ℏ)` of a black hole whose horizon
has radius `r` (so horizon area `A = 4π r²`), in terms of Boltzmann's constant `k`,
Newton's constant `G`, the reduced Planck constant `hbar` and the speed of light `c`. -/

noncomputable def schwarzschildEnergy (G c r : ℝ) : ℝ := r * c ^ 4 / (2 * G)

/-- The Schwarzschild radius `r = 2 G E / c⁴` associated with an energy `E`. -/
