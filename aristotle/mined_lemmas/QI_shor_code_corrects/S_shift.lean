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

lemma S_shift (u x y : Bits) (a b : Bool) :
    (∑ v : Bits, chi u v * f a (bxor v x) * f b (bxor v y))
      = chi u x * ∑ c : Bits, chi u c * f a c * f b (bxor c (bxor x y)) := by
  rw [← sum_bxor_shift (fun v => chi u v * f a (bxor v x) * f b (bxor v y)) x, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro c _
  rw [bxor_self_cancel, bxor_assoc, chi_bxor_right]
  ring

/-! ## Support conditions coming from single-qubit errors -/

