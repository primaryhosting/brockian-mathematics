import Mathlib

/-!
# Unruh Effect
Category: Frontier Phys
Target: Phys.unruh_effect
Statement: State the Unruh temperature T = ℏa/(2πck) seen by a uniformly accelerated observer.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

/-- The physical constants entering the Unruh formula: the reduced Planck constant `hbar`,
the speed of light `c` and Boltzmann's constant `kB`, all positive. -/
structure Constants where
  hbar : ℝ
  c : ℝ
  kB : ℝ
  hbar_pos : 0 < hbar
  c_pos : 0 < c
  kB_pos : 0 < kB

variable (C : Constants)

/-- The **Unruh temperature** `T = ℏ a / (2 π c k_B)` associated with proper acceleration `a`. -/

lemma cosh_two_pi_I : Complex.cosh (2 * (Real.pi : ℂ) * Complex.I) = 1 := by
  rw [Complex.cosh_mul_I, Complex.cos_two_pi]

