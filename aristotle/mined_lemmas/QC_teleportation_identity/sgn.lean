import Mathlib

/-!
# Teleportation Identity
Category: Quantum Computing
Target: QC.teleportation_identity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC


def sgn (a i : Bool) : ℂ := if a && i then -1 else 1

/-- Amplitudes of the Bell basis state `|B_{a,b}⟩ = (1/√2) Σ_i (-1)^(a i) |i, i ⊕ b⟩`
on the two-qubit computational basis. -/
