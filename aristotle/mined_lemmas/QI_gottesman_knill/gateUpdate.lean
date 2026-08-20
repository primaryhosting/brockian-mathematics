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

def gateUpdate {n : ℕ} : Gate n → Pauli n → Pauli n
  | .H q => fun p =>
      ⟨p.s + 2 * lift2 (p.x q * p.z q), Function.update p.x q (p.z q),
        Function.update p.z q (p.x q)⟩
  | .S q => fun p => ⟨p.s + lift2 (p.x q), p.x, Function.update p.z q (p.x q + p.z q)⟩
  | .CZ c t => fun p =>
      ⟨p.s + 2 * lift2 (p.x c * p.x t), p.x,
        fun r => p.z r + (if r = t then p.x c else 0) + (if r = c then p.x t else 0)⟩

/-- The qubits a gate acts on. -/
