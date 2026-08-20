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

lemma S_of_not_blocky (u x y : Bits) (a b : Bool) (hd : ¬ Blocky (bxor x y)) :
    (∑ v : Bits, chi u v * f a (bxor v x) * f b (bxor v y)) = 0 := by
  rw [S_shift]
  have : ∀ c : Bits, chi u c * f a c * f b (bxor c (bxor x y)) = 0 := by
    intro c
    rw [mul_assoc, f_mul_shift_eq_zero hd a b c, mul_zero]
  simp [Finset.sum_congr rfl (fun c _ => this c)]

