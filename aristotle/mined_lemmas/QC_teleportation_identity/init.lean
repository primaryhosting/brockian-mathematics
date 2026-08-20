import Mathlib

/-!
# Teleportation Identity
Category: Quantum Computing
Target: QC.teleportation_identity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC


noncomputable def init (psi : Bool → ℂ) (i j k : Bool) : ℂ :=
  psi i * invSqrt2 * (if j = k then 1 else 0)

/-- The (unnormalized) state of the receiver's qubit after a Bell measurement with
outcome `(a, b)` on the first two qubits. -/
