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

open scoped Real
open MeasureTheory Matrix

namespace Frontier

/-! ## The classical (local hidden variable) side -/

/-- The pointwise CHSH bound: if four numbers `a₀, a₁, b₀, b₁` have absolute value at most `1`
(the possible outcomes, or local averages of outcomes, of `±1`-valued measurements), then the
CHSH combination is bounded by `2` in absolute value. -/

noncomputable def constLHV : LHVModel where
  Ω := Unit
  measurable := inferInstance
  μ := Measure.dirac ()
  prob := inferInstance
  a := fun _ _ => 1
  b := fun _ _ => 1
  ha := by simp
  hb := by simp
  hint := fun _ _ => by
    have : IsProbabilityMeasure (Measure.dirac (α := Unit) ()) := inferInstance
    simp using integrable_const (μ := Measure.dirac (α := Unit) ()) (1 : ℝ)

/-- The classical CHSH bound `2` is attained, so the inequality of `LHVModel.abs_chsh_le_two`
is sharp. -/
