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

lemma flP_emb_eq_iff (p q : P1) (i j : Fin 9) (t t' : T) :
    (flP p i (emb t) = flP q j (emb t')) ↔ (compat p q i j = true ∧ t = t') := by
  cases p <;> cases q <;>
    simp [flP, compat, flips, emb_inj, flip_emb_ne, flip_emb_ne', flip_emb_eq]

/-! ## The character sums -/

