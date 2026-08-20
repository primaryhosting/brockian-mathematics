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

lemma gateUpdate_local {n : ℕ} (g : Gate n) (p : Pauli n) (r : Fin n) (hr : r ∉ gateSupport g) :
    (gateUpdate g p).x r = p.x r ∧ (gateUpdate g p).z r = p.z r := by
  cases g with
  | H q =>
      have : r ≠ q := by simpa [gateSupport] using hr
      simp [gateUpdate, Function.update_of_ne this]
  | S q =>
      have : r ≠ q := by simpa [gateSupport] using hr
      simp [gateUpdate, Function.update_of_ne this]
  | CZ c t =>
      have h : r ≠ c ∧ r ≠ t := by
        simpa [gateSupport, not_or] using hr
      simp [gateUpdate, h.1, h.2]

/-! ## Circuits -/

/-- The unitary implemented by a circuit (a list of gates applied left to right). -/
