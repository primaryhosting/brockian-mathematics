/-
# Bell Theorem
Category: Frontier Physics
Target: Frontier.bell_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open MeasureTheory Real

namespace Frontier

/-- **Pointwise CHSH bound.** For real numbers of absolute value at most `1`,
the CHSH combination `a₁b₁ + a₁b₂ + a₂b₁ - a₂b₂` has absolute value at most `2`. -/

theorem quantum_chsh_value :
    quantumCorr false false + quantumCorr false true + quantumCorr true false
      - quantumCorr true true = 2 * Real.sqrt 2 := by
  have h4 : Real.cos (π / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
  have h34 : Real.cos (π / 2 - -(π / 4)) = -(Real.sqrt 2 / 2) := by
    have : π / 2 - -(π / 4) = π - π / 4 := by ring
    rw [this, Real.cos_pi_sub, h4]
  simp only [quantumCorr, aliceAngle, bobAngle]
  rw [show (0 : ℝ) - π / 4 = -(π / 4) by ring, Real.cos_neg, h4,
    show (0 : ℝ) - -(π / 4) = π / 4 by ring, h4,
    show π / 2 - π / 4 = π / 4 by ring, h4, h34]
  ring

/-- `2√2 > 2`: the quantum CHSH value exceeds the classical bound. -/
