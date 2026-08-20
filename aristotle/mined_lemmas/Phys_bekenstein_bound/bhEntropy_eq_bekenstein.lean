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

theorem bhEntropy_eq_bekenstein {k G hbar c r : ℝ} (hG : G ≠ 0) (hhbar : hbar ≠ 0)
    (hc : c ≠ 0) :
    bhEntropy k G hbar c r = 2 * π * k * r * schwarzschildEnergy G c r / (hbar * c) := by
  unfold bhEntropy schwarzschildEnergy
  field_simp

/-- **The Bekenstein bound.** A physical system of energy `E ≥ 0` confined to a region of
radius `R` has entropy `S ≤ 2π k R E / (ℏ c)`.

The physical input is Susskind's collapse argument, encoded as hypotheses:
* `hfit` : the system is not already inside its own Schwarzschild radius, i.e.
  `2 G E / c⁴ ≤ R`;
* `hGSL` : by the second law of thermodynamics, collapsing the system into a black hole
  cannot decrease entropy, so `S` is at most the Bekenstein–Hawking entropy of the
  black hole of energy `E`.

From these, the bound follows from the key lemma
`bhEntropy_eq_bekenstein` together with monotonicity in the radius. -/
