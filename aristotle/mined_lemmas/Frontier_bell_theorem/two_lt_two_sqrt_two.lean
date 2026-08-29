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

theorem two_lt_two_sqrt_two : (2 : ℝ) < 2 * Real.sqrt 2 := by
  have h : (1 : ℝ) < Real.sqrt 2 := by
    have : Real.sqrt 1 < Real.sqrt 2 := by
      apply Real.sqrt_lt_sqrt <;> norm_num
    simpa using this
  linarith

/-- **Bell's theorem.**  No local hidden-variable model reproduces the quantum-mechanical
correlations: for any finite hidden-variable space with a probability weight `p` and
outcome functions `A`, `B` taking values in `[-1, 1]` (Alice's depending only on her setting,
Bob's only on his), the resulting correlations cannot equal the quantum predictions
`QuantumCorr`, because the latter have CHSH value `2√2 > 2` while every local model obeys
`|CHSH| ≤ 2`. -/
