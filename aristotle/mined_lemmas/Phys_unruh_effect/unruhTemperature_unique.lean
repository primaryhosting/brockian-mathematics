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

theorem unruhTemperature_unique (hbar a c kB : ℝ) (hhbar : 0 < hbar) (ha : 0 < a) (hc : 0 < c)
    (hkB : 0 < kB) (T : ℝ) (hT : 0 < T) :
    hbar / (kB * T) = 2 * Real.pi * c / a ↔ T = unruhTemperature hbar a c kB := by
  have hpi := Real.pi_pos
  constructor
  · intro h
    unfold unruhTemperature
    field_simp at h ⊢
    linarith [h]
  · rintro rfl
    exact unruh_kms hbar a c kB hhbar.ne' ha.ne' hc.ne' hkB.ne'

/-- The response of the accelerated detector, governed by the Rindler factor
`1 / (exp (2 π c ω / a) - 1)`, is exactly a Planck spectrum at the Unruh temperature. -/
