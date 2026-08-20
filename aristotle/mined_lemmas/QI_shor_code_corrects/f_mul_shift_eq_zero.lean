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

lemma f_mul_shift_eq_zero {d : Bits} (hd : ¬ Blocky d) (a b : Bool) (c : Bits) :
    f a c * f b (bxor c d) = 0 := by
  by_cases hc : Blocky c
  · by_cases hcd : Blocky (bxor c d)
    · exact absurd (bxor_cancel_left c d ▸ blocky_bxor hc hcd) hd
    · simp [f_eq_zero_of_not_blocky _ hcd]
  · simp [f_eq_zero_of_not_blocky _ hc]

