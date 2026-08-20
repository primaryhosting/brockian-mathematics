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

theorem schwarzschildEnergy_schwarzschildRadius {G c E : ℝ} (hG : G ≠ 0) (hc : c ≠ 0) :
    schwarzschildEnergy G c (schwarzschildRadius G c E) = E := by
  unfold schwarzschildEnergy schwarzschildRadius
  field_simp

/-- **Key lemma.** For a Schwarzschild black hole of horizon radius `r`, the
Bekenstein–Hawking entropy saturates the Bekenstein expression `2π k r E / (ℏ c)`,
where `E` is the black hole's energy. -/
