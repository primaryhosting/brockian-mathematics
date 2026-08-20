import Mathlib

/-!
# Teleportation Identity
Category: Quantum Computing
Target: QC.teleportation_identity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC


noncomputable def measured (psi : Bool → ℂ) (a b k : Bool) : ℂ :=
  ∑ i : Bool, ∑ j : Bool, (starRingEnd ℂ) (bell a b i j) * init psi i j k

/-- The receiver's state after applying the Pauli correction `Z^a X^b` dictated by the
classical outcome `(a, b)` and renormalizing (the measurement outcome has probability
`1/4`, so the correct normalization factor is `2`). -/
