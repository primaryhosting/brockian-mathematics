/-
# Gottesman Knill
Category: Frontier Qi
Target: QI.gottesman_knill
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Gottesman Knill
Category: Frontier Qi
Target: QI.gottesman_knill
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Matrix

namespace QI

/-! ## Bit vectors -/

/-- Computational basis labels for `n` qubits: bit strings of length `n`. -/
abbrev Bits (n : ℕ) := Fin n → Bool

variable {n : ℕ}

/-- Bitwise `xor` of two bit strings. -/

def stepGate : Gate n → Pauli n → Pauli n
  | .H j => fun p =>
      { ph := p.ph + (if p.xs j && p.zs j then 2 else 0)
        xs := bxor p.xs (condVec (xor (p.xs j) (p.zs j)) j)
        zs := bxor p.zs (condVec (xor (p.xs j) (p.zs j)) j) }
  | .S j => fun p =>
      { ph := p.ph + (if p.xs j then 1 else 0)
        xs := p.xs
        zs := bxor p.zs (condVec (p.xs j) j) }
  | .CX j k _ => fun p =>
      { ph := p.ph
        xs := cxf j k p.xs
        zs := czf j k p.zs }

/-- The set of wires a gate acts on. -/
