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

lemma tp_conj {n : ℕ} (A P P' : Fin n → Matrix (ZMod 2) (ZMod 2) ℂ) (c : Fin n → ℂ)
    (h : ∀ r, A r * P r = c r • (P' r * A r)) :
    tp A * tp P = (∏ r, c r) • (tp P' * tp A) := by
  rw [tp_mul, tp_mul, ← tp_smul]
  exact congrArg tp (funext h)

