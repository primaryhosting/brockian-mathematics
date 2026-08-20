/-
# Shor Code Corrects
Category: Frontier Qi
Target: QI.shor_code_corrects
Statement: The 9-qubit Shor code corrects an arbitrary single-qubit error.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Shor Code Corrects
Category: Frontier Qi
Target: QI.shor_code_corrects
Statement: The 9-qubit Shor code corrects an arbitrary single-qubit error.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace QI

/-- Index set of the nine qubits: three blocks of three. -/
abbrev Idx : Type := Fin 3 × Fin 3

/-- Computational basis states of the nine qubits are bit strings. -/
abbrev Bits : Type := Idx → Bool

/-- Pointwise `xor` of two bit strings. -/

lemma sign_merge3 (s w1 ea eb : Bool) :
    ((if s && w1 then (-1 : ℤ) else 1) * (if s && ea then (-1 : ℤ) else 1))
        * (if s && eb then (-1 : ℤ) else 1)
      = if s && (xor w1 (xor ea eb)) then (-1 : ℤ) else 1 := by
  revert s w1 ea eb; decide

