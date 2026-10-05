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

theorem unruh_kms (hbar a c kB : ℝ) (hhbar : hbar ≠ 0) (ha : a ≠ 0) (hc : c ≠ 0)
    (hkB : kB ≠ 0) :
    hbar / (kB * unruhTemperature hbar a c kB) = 2 * Real.pi * c / a := by
  unfold unruhTemperature
  field_simp

