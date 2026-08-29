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

lemma op_cw (p : P1) (i : Fin 9) (k : Bool) :
    op p i (cw k) = nrm • ∑ t : T, (sgnc k t * ampP p i (emb t)) • eb (flP p i (emb t)) := by
  rw [cw, map_smul, map_sum]
  congr 1
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [map_smul, op_eb, smul_smul]


/-! ## When two Pauli-shifted basis states coincide -/

/-- Whether a Pauli permutes computational basis labels. -/
