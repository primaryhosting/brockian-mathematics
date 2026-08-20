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

noncomputable def qB : Fin 2 → Matrix (Fin 4) (Fin 4) ℝ
  | 0 => !![s, s, 0, 0; s, -s, 0, 0; 0, 0, s, s; 0, 0, s, -s]
  | 1 => !![s, -s, 0, 0; -s, -s, 0, 0; 0, 0, s, -s; 0, 0, -s, -s]

/-- The maximally entangled state `(|00⟩ + |11⟩)/√2`. -/
