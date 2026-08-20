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

lemma circuitMatrix_unitary {n : ℕ} (gs : List (Gate n)) :
    circuitMatrix gs * (circuitMatrix gs)ᴴ = 1 := by
  induction gs with
  | nil => simp [circuitMatrix]
  | cons g gs ih =>
      rw [circuitMatrix, Matrix.conjTranspose_mul, ← Matrix.mul_assoc,
        Matrix.mul_assoc (circuitMatrix gs), gateMatrix_unitary, Matrix.mul_one, ih]

