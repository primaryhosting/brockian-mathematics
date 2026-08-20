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

theorem qCorr_chsh : qCorr 0 0 + qCorr 0 1 + qCorr 1 0 - qCorr 1 1 = 2 * Real.sqrt 2 := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hne : Real.sqrt 2 ≠ 0 := by positivity
  simp only [qCorr_eq]
  norm_num [s]
  field_simp
  linarith [h2]

/-- **Bell's theorem.**  There is a quantum model (two spin-`1/2` particles in a maximally
entangled state, with two `±1`-valued spin observables on each side, Alice's commuting with
Bob's) whose correlations `qCorr` achieve the CHSH value `2√2`; and *no* local hidden variable
model reproduces these correlations, since every local hidden variable model obeys the CHSH
bound `|E(0,0) + E(0,1) + E(1,0) - E(1,1)| ≤ 2 < 2√2`. -/
