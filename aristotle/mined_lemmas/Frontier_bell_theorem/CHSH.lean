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

noncomputable def chsh (M : LHVModel Ω) : ℝ :=
  M.corr 0 0 + M.corr 0 1 + M.corr 1 0 - M.corr 1 1

end LHVModel

/-- **CHSH inequality**: every local hidden-variable model satisfies `|CHSH| ≤ 2`. -/
