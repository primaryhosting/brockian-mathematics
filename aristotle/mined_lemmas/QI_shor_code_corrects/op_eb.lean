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

lemma op_eb (p : P1) (i : Fin 9) (c : Q) :
    op p i (eb c) = ampP p i c • eb (flP p i c) := by
  rw [op, mkOp_eb _ _ (flP_invol p i)]
  congr 1
  cases p <;> simp [coP, ampP, flP, flipAt_self] <;> cases c i <;> simp

/-! ## The Shor codewords -/

/-- Index type for the eight basis states in the support of the codewords. -/
abbrev T := Bool × Bool × Bool

/-- The block a qubit belongs to. -/
