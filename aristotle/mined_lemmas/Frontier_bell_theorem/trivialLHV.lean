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

noncomputable def trivialLHV : LHVModel Unit where
  μ := Measure.dirac ()
  isProb := inferInstance
  A₁ := fun _ => 1
  A₂ := fun _ => 1
  B₁ := fun _ => 1
  B₂ := fun _ => 1
  hA₁ := by norm_num
  hA₂ := by norm_num
  hB₁ := by norm_num
  hB₂ := by norm_num
  intAB := by
    intro i j
    simp

/-- The classical CHSH bound is attained, hence sharp. -/
