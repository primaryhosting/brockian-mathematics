/-
# Box Level 7
Category: Quantum Physics
Target: QPhys.box_level_7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Box Level 7
Category: Quantum Physics
Target: QPhys.box_level_7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QPhys

/-- Energy levels of a particle of mass `m` in a one-dimensional infinite square well
of width `L`:  `Eₙ = n² π² ħ² / (2 m L²)`. -/

noncomputable def boxEnergy (ħ m L : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ 2 * Real.pi ^ 2 * ħ ^ 2 / (2 * m * L ^ 2)

/-- For the one-dimensional infinite square well, the ratio of the seventh energy level
to the ground-state energy is `7² = 49`. -/
