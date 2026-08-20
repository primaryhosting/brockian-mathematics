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

theorem qCorr_eq (i j : Fin 2) :
    qCorr i j = if i = 1 ∧ j = 1 then -s else s := by
  fin_cases i <;> fin_cases j <;>
    · simp [qCorr, qA, qB, qPsi, Matrix.mul_apply, Matrix.mulVec, dotProduct,
        Fin.sum_univ_four]
      first
        | linear_combination (2 * s) * s_sq
        | linear_combination (-2 * s) * s_sq

/-- The quantum CHSH value is `2√2`, exceeding the classical bound `2`. -/
