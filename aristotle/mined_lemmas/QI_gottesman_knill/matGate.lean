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

noncomputable def matGate : Gate n → Matrix (Bits n) (Bits n) ℂ
  | .H j => fun b c => if agreeOff j b c then invSqrt2 * sgn1 (b j) (c j) else 0
  | .S j => fun b c => if b = c then (if b j then Complex.I else 1) else 0
  | .CX j k _ => fun b c => if b = cxf j k c then 1 else 0

/-- The classical (tableau) update rule corresponding to a Clifford generator. -/
