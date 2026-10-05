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

lemma inner_cw_diag (k : Bool) : inner ℂ (cw k) (cw k) = 1 := by
  have hc : compat I I 0 0 = true := by decide
  rw [← op_I 0 (cw k), inner_op_cw_pos _ _ _ _ _ _ hc]
  simp only [summand_diag, ampP_I, map_one, one_mul]
  simp
  norm_num

