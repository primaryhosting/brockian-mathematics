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

lemma inner_op_cw_pos (p q : P1) (i j : Fin 9) (k l : Bool) (hc : compat p q i j = true) :
    inner ℂ (op p i (cw k)) (op q j (cw l)) =
      (1/8 : ℂ) * ∑ t : T, conj (sgnc k t * ampP p i (emb t)) * (sgnc l t * ampP q j (emb t)) := by
  rw [inner_op_cw, if_pos hc]

