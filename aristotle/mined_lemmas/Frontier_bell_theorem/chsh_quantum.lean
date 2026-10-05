/-!
# Bell Theorem
Category: Frontier Physics
Target: Frontier.bell_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Frontier

open Finset

/-- The CHSH combination of four correlation values. -/

theorem chsh_quantum : CHSH QuantumCorr = 2 * Real.sqrt 2 := by
  have h4 : Real.cos (Real.pi / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
  have h34 : Real.cos (3 * Real.pi / 4) = -(Real.sqrt 2 / 2) := by
    have : (3 : ℝ) * Real.pi / 4 = Real.pi - Real.pi / 4 := by ring
    rw [this, Real.cos_pi_sub, h4]
  simp only [CHSH, QuantumCorr, alphaAngle, betaAngle, if_true, if_false]
  have e1 : (0 : ℝ) - Real.pi / 4 = -(Real.pi / 4) := by ring
  have e2 : (0 : ℝ) - -(Real.pi / 4) = Real.pi / 4 := by ring
  have e3 : Real.pi / 2 - Real.pi / 4 = Real.pi / 4 := by ring
  have e4 : Real.pi / 2 - -(Real.pi / 4) = 3 * Real.pi / 4 := by ring
  rw [e1, e2, e3, e4, Real.cos_neg, h4, h34]
  ring

