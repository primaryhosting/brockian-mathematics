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

noncomputable def bhEntropy (k G hbar c r : ℝ) : ℝ := π * k * c ^ 3 * r ^ 2 / (G * hbar)

/-- The energy `E = M c² = r c⁴ / (2G)` of a Schwarzschild black hole of horizon radius `r`. -/
