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

def blkVal (t : T) : Fin 3 → Bool := ![t.1, t.2.1, t.2.2]

/-- `emb t` is the basis label whose three blocks of three qubits are constant,
equal to `t.1`, `t.2.1`, `t.2.2` respectively. -/
