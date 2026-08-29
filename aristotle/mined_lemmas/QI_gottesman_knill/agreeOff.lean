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

def agreeOff (j : Fin n) (b c : Bits n) : Prop := ∀ i, i ≠ j → b i = c i

instance (j : Fin n) (b c : Bits n) : Decidable (agreeOff j b c) := by
  unfold agreeOff; infer_instance

/-- The action of `CNOT` with control `j` and target `k` on basis labels. -/
