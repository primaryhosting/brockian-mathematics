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

noncomputable def corr (M : LHVModel Ω) (i j : Fin 2) : ℝ :=
  ∫ ω, (if i = 0 then M.A₁ ω else M.A₂ ω) * (if j = 0 then M.B₁ ω else M.B₂ ω) ∂M.μ

/-- The CHSH combination of the four correlations of a local hidden-variable model. -/
