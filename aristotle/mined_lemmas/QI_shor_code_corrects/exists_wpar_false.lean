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

lemma exists_wpar_false {u : Bits} {k l : Idx} (h : ∀ q, u q = true → q = k ∨ q = l) :
    ∃ m : Fin 3, wpar u m = false := by
  obtain ⟨m, hm1, hm2⟩ := exists_fin3_ne k.1 l.1
  refine ⟨m, ?_⟩
  have key : ∀ p : Fin 3, u (m, p) = false := by
    intro p
    by_contra hp
    have hp' : u (m, p) = true := by simpa using hp
    rcases h _ hp' with h' | h'
    · exact hm1 (congrArg Prod.fst h')
    · exact hm2 (congrArg Prod.fst h')
  simp [wpar, key 0, key 1, key 2]

