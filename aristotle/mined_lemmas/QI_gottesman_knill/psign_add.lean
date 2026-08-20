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

lemma psign_add (s t : ZMod 2) : psign (s + t) = psign s * psign t := by
  rcases zmod2_cases s with rfl | rfl <;> rcases zmod2_cases t with rfl | rfl <;> simp [psign]

