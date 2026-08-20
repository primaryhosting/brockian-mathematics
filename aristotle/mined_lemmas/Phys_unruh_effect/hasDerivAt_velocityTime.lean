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

lemma hasDerivAt_velocityTime {a : ℝ} (τ : ℝ) :
    HasDerivAt (fun τ : ℝ => Real.cosh (a * τ / C.c)) ((a / C.c) * Real.sinh (a * τ / C.c)) τ := by
  have h : HasDerivAt (fun τ : ℝ => a * τ / C.c) (a / C.c) τ := by
    simpa [mul_comm, mul_div_assoc] using
      ((hasDerivAt_id τ).const_mul a).div_const C.c
  simpa [mul_comm] using h.cosh

/-- The four-acceleration: `x''(τ) = a cosh (a τ / c)`. -/
