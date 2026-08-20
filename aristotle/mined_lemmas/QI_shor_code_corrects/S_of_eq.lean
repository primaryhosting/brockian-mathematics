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

lemma S_of_eq (u x : Bits) (a b : Bool) :
    (∑ v : Bits, chi u v * f a (bxor v x) * f b (bxor v x))
      = chi u x * ∏ m : Fin 3, (if xor (wpar u m) (xor a b) then (0 : ℤ) else 2) := by
  rw [S_shift]
  have hxx : bxor x x = bzero := by funext q; simp [bxor, bzero]
  simp only [hxx, bxor_bzero]
  rw [T_eval]

/-! ## From integer sums to inner products -/

