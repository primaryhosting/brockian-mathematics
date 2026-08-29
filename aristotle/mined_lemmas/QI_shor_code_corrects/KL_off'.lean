import Mathlib

/-!
# Shor Code Corrects
Category: Frontier Qi
Target: QI.shor_code_corrects
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open ComplexConjugate

namespace QI

/-! ## The 9-qubit Hilbert space -/

/-- Labels for the computational basis of 9 qubits. -/
abbrev Q := Fin 9 → Bool

/-- The state space of 9 qubits, `ℂ^(2^9)` with its standard Hermitian inner product. -/
abbrev H := EuclideanSpace ℂ Q

/-- Flip the `i`-th bit of a basis label. -/

lemma KL_off' (p q : P1) (i j : Fin 9) :
    inner ℂ (op p i (cw true)) (op q j (cw false)) = 0 := by
  have h := KL_off q p j i
  rw [← inner_conj_symm] at h
  simpa using h

