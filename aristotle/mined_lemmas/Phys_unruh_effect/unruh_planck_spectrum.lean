/-
/-!
# Unruh Effect
Category: Frontier Phys
Target: Phys.unruh_effect
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/

import Mathlib

/-!
# Unruh Effect
Category: Frontier Phys
Target: Phys.unruh_effect
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open scoped Real

set_option maxHeartbeats 1000000

namespace Phys

/-! ## The Unruh temperature -/

/-- The Unruh temperature `T = ℏ a / (2 π c k_B)` seen by an observer with proper
acceleration `a`. -/

theorem unruh_planck_spectrum (hbar a c kB : ℝ) (hhbar : 0 < hbar) (ha : 0 < a) (hc : 0 < c)
    (hkB : 0 < kB) (ω : ℝ) :
    planckOccupation hbar kB (unruhTemperature hbar a c kB) ω
      = 1 / (Real.exp (2 * Real.pi * c * ω / a) - 1) := by
  unfold planckOccupation
  have hkms := unruh_kms hbar a c kB hhbar.ne' ha.ne' hc.ne' hkB.ne'
  have : hbar * ω / (kB * unruhTemperature hbar a c kB) = 2 * Real.pi * c * ω / a := by
    rw [mul_comm hbar ω, mul_div_assoc, hkms]; ring
  rw [this]

/-! ## The Unruh effect -/

/--
**The Unruh effect.**

An observer moving with constant proper acceleration `a` (hypotheses: `ℏ, a, c, k_B > 0`)
perceives the Minkowski vacuum as a thermal bath at the *Unruh temperature*

  `T = ℏ a / (2 π c k_B)`.

The statement packages the standard derivation:

1. the hyperbolic worldline `x = (c²/a) cosh(aτ/c)`, `t = (c/a) sinh(aτ/c)` is parametrised
   by proper time (`c² (dt/dτ)² - (dx/dτ)² = c²`) and has constant proper acceleration `a`;
2. its Euclidean continuation is periodic in imaginary proper time with period
   `β = 2 π c / a`;
3. this KMS period corresponds to the inverse temperature `ℏ / (k_B T)` for, and only for,
   `T = ℏ a / (2 π c k_B) = unruhTemperature ℏ a c k_B`, which is positive;
4. consequently the detector response `1 / (exp (2 π c ω / a) - 1)` is exactly a Planck
   spectrum at that temperature.
-/
