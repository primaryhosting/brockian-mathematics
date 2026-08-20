/-
# Gottesman Knill
Category: Frontier Qi
Target: QI.gottesman_knill
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` lines to precede any module docstring `/-! ... -/`,
-- so the header above is a plain comment and is repeated as a docstring below.)

import Mathlib

/-!
# Gottesman Knill
Category: Frontier Qi
Target: QI.gottesman_knill
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Matrix

namespace QI

/-! ## Phases and signs -/

/-- Computational basis labels for `n` qubits: bit strings of length `n`. -/
abbrev Bits (n : ℕ) : Type := Fin n → ZMod 2

/-- The fourth root of unity `i ^ s` attached to `s : ZMod 4`. -/

lemma ph_two_lift (t : ZMod 2) : ph (2 * lift2 t) = psign t := by
  rcases zmod2_cases t with rfl | rfl
  · simp
  · rw [show (2 * lift2 (1 : ZMod 2) : ZMod 4) = 2 from by decide]
    simp [ph, psign, show ZMod.val (2 : ZMod 4) = 2 from by decide, pow_two, Complex.I_mul_I]

