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

theorem constLHV_chsh :
    constLHV.corr 0 0 + constLHV.corr 0 1 + constLHV.corr 1 0 - constLHV.corr 1 1 = 2 := by
  have h : ∀ i j, constLHV.corr i j = 1 := by
    intro i j
    simp [LHVModel.corr, constLHV]
  rw [h, h, h, h]
  norm_num

/-- Alice's observables: `Z ⊗ I` and `X ⊗ I` on two qubits (real `4 × 4` matrices). -/
