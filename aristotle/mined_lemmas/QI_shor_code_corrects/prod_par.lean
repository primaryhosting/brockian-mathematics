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

lemma prod_par (t : Fin 3 → Bool) (e : Bool) :
    (if e then ∏ m : Fin 3, (if t m then (-1 : ℤ) else 1) else 1)
      = ∏ m : Fin 3, (if t m && e then (-1 : ℤ) else 1) := by
  cases e <;> simp

/-- The basic sum: `T u a b = ∑_c χ_u(c) f_a(c) f_b(c)`. -/
