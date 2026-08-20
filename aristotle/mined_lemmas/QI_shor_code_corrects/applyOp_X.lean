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

lemma applyOp_X (k : Idx) (ψ : Bits → ℂ) :
    applyOp k (fun s t => if s = t then 0 else 1) ψ = fun v => ψ (bxor v (bone k)) := by
  funext v
  unfold applyOp
  have h := update_bxor k v
  cases hv : v k <;> rw [hv] at h <;> simp <;> rw [← h] <;> simp

/-! ## A consequence: a single-qubit error preserves the geometry of the code space -/

/-- A general state of the logical qubit, with amplitudes `co false`, `co true`. -/
