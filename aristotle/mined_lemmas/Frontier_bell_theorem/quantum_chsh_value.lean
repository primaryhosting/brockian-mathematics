/-
# Bell Theorem
Category: Frontier Physics
Target: Frontier.bell_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Bell Theorem
Category: Frontier Physics
Target: Frontier.bell_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory

namespace Frontier

/-- Pointwise CHSH inequality: for outcomes in `[-1, 1]`, the CHSH combination is
bounded by `2`. -/

theorem quantum_chsh_value :
    Real.cos (Real.pi / 4) + Real.cos (Real.pi / 4) + Real.cos (Real.pi / 4)
      - Real.cos (3 * Real.pi / 4) = 2 * Real.sqrt 2 ∧ 2 < 2 * Real.sqrt 2 := by
  have hcos : Real.cos (Real.pi / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
  have hcos3 : Real.cos (3 * Real.pi / 4) = -(Real.sqrt 2 / 2) := by
    have : (3 : ℝ) * Real.pi / 4 = Real.pi - Real.pi / 4 := by ring
    rw [this, Real.cos_pi_sub, hcos]
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  refine ⟨by rw [hcos, hcos3]; ring, ?_⟩
  nlinarith [hs, Real.sqrt_nonneg 2]

/-- **Bell's theorem**: no local hidden-variable model reproduces the quantum-mechanical
correlations of the singlet state at the optimal CHSH measurement angles, namely
`E(1,1) = E(1,2) = E(2,1) = √2/2` and `E(2,2) = -√2/2`, whose CHSH value is `2√2 > 2`. -/
