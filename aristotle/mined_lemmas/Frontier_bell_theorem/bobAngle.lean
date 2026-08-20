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

noncomputable def bobAngle : Bool → ℝ
  | false => π / 4
  | true => -(π / 4)

/-- The quantum-mechanical correlation `cos (α - β)` for two spin measurements at angles
`α` and `β` (in the appropriate state). -/
