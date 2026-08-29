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

theorem trivialLHV_chsh : trivialLHV.chsh = 2 := by
  simp [LHVModel.chsh, LHVModel.corr, trivialLHV]
  norm_num

/-- Quantum mechanics predicts, for the singlet state, the correlation `cos θ` where `θ` is the
angle between the two measurement directions. At the optimal CHSH angles the four correlations
are `√2/2, √2/2, √2/2, -√2/2`, with CHSH value `2√2`, which exceeds the classical bound `2`. -/
